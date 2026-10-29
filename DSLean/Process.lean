/- Running an external program with a deadline, a bounded output, and the cleanup of its process group -/
import Lean

open Lean

namespace DSLean

/-- An external program, found through an environment variable (DSLean's convention, as with
`DSLEAN_SAGE_PATH`, `DSLEAN_GAPPA_PATH` and `DSLEAN_M2_PATH`) and otherwise run by its default
name. -/
structure ExternalTool where
  /-- The tool's name, for messages. -/
  name : String
  /-- The environment variable that names the program. -/
  envVar : String
  /-- The program run when the variable is not set. -/
  default : String
deriving Inhabited, Repr

/-- The program of `tool`: the value of its variable, else its default. -/
def ExternalTool.program (tool : ExternalTool) : IO String :=
  return (← IO.getEnv tool.envVar).getD tool.default

/-- The limits of one run. -/
structure RunLimits where
  /-- Deadline of the run, from the start of the program, in milliseconds. Ending the process
  group and draining the pipes afterwards take at most about two more seconds. -/
  timeoutMs : Nat := 120000
  /-- Largest standard output, in bytes; a longer one fails the run. -/
  maxOutputBytes : Nat := 16 * 1024 * 1024
  /-- Largest part of the standard error that is kept, in bytes; the rest is read and dropped,
  and `RunResult.stderrTruncated` says so. -/
  maxErrorBytes : Nat := 4096
deriving Inhabited, Repr

/-- A run that ended within its limits. -/
structure RunResult where
  /-- The program's exit code. -/
  exitCode : UInt32
  /-- Its standard output. -/
  stdout : String
  /-- The first `maxErrorBytes` bytes of its standard error. -/
  stderr : String
  /-- Whether the standard error was longer than `maxErrorBytes` bytes. -/
  stderrTruncated : Bool
deriving Inhabited, Repr

/-- Why a run has no result. -/
inductive RunFailure where
  /-- The program could not be started. -/
  | unavailable (reason : String)
  /-- The program ran past the deadline; its process group was ended. -/
  | timeout (milliseconds : Nat)
  /-- The cancellation token was set; the process group was ended. -/
  | cancelled
  /-- The standard output was longer than the bound. -/
  | overflow (bytes : Nat)
  /-- The standard output is not UTF-8. -/
  | notUTF8
  /-- The standard output was still open two seconds after the process group was ended. -/
  | unclosed
  /-- Reading or writing a pipe, or waiting for the program, failed. -/
  | io (error : String)
deriving Inhabited, Repr

/-- Write `text` to a pipe; the handle is closed when this task drops it, which gives the
program the end of its input. -/
private def writeAll (handle : IO.FS.Handle) (text : String) : IO Unit := do
  handle.putStr text
  handle.flush

/-- Read a pipe to its end, keeping its first `limit` bytes; the rest is read and dropped, so
that a program writing more cannot block on a full pipe, and the flag records the overflow. -/
private partial def readBounded (handle : IO.FS.Handle) (limit : Nat) : IO (ByteArray × Bool) :=
  go ByteArray.empty false
where
  go (kept : ByteArray) (overflow : Bool) : IO (ByteArray × Bool) := do
    let chunk ← handle.read 65536
    if chunk.isEmpty then return (kept, overflow)
    if kept.size + chunk.size ≤ limit then go (kept ++ chunk) overflow
    else go (kept ++ chunk.extract 0 (limit - kept.size)) true

/-- Wait at most `ms` milliseconds for `child` to exit, reaping it; whether it did (an error of
`tryWait`, such as a child already reaped, counts as exited). -/
private def reapWithin {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (ms : Nat) : IO Bool := do
  let stop := (← IO.monoMsNow) + ms
  repeat
    if ← (try return (← child.tryWait).isSome catch _ => return true) then return true
    if (← IO.monoMsNow) > stop then return false
    IO.sleep 5
  return false

/-- The program that sends `SIGKILL`: the system's `kill`, at a fixed absolute path, never
looked up in `PATH`. Lean exposes no direct `kill (2)`, so the cleanup of `terminateGroup`
trusts this program as it trusts the operating system. -/
def killProgram : IO (Option String) := do
  for path in ["/usr/bin/kill", "/bin/kill"] do
    if ← (System.FilePath.mk path).pathExists then return some path
  return none

/-- Send `SIGKILL` to the process group `group` through `killProgram`. The helper runs in a
session of its own and is reaped within one second; on overrun it is sent `SIGTERM`, and in
every case its own group is then signalled, so that nothing it might leave behind outlives it. -/
def killGroup (group : UInt32) : IO Unit := do
  let some program ← killProgram | return
  let helper ← IO.Process.spawn
    { cmd := program, args := #["-KILL", "--", s!"-{group}"], stdin := .null,
      stdout := .null, stderr := .null, setsid := true }
  unless ← reapWithin helper 1000 do
    try helper.kill catch _ => pure ()
    discard <| reapWithin helper 500
  try helper.kill catch _ => pure ()

/-- End the process group of `child`, which was started with `setsid` (so its group is its
pid): `SIGTERM` to the group through `Child.kill`, a bounded wait for the leader, then `SIGKILL`
to the whole group, which also ends descendants that ignore `SIGTERM`, then a bounded reap. With
`reaped` the leader has already been waited for and only its group is signalled. Errors (the
group is already gone) are ignored. A process in an uninterruptible wait may stay unreaped. -/
def terminateGroup {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (reaped : Bool := false) : IO Unit := do
  try child.kill catch _ => pure ()
  unless reaped do discard <| reapWithin child 2000
  try killGroup child.pid catch _ => pure ()
  unless reaped do discard <| reapWithin child 2000

/-- Whether the run is cancelled: the task's own flag, or the given cancellation token (the
elaborator's, for a run started by a command or tactic). -/
private def cancelled (token? : Option IO.CancelToken) : IO Bool := do
  if ← IO.checkCanceled then return true
  match token? with
  | some token => token.isSet
  | none => return false

/-- Wait for `task` until `deadline` (on `IO.monoMsNow`) without blocking past it; `none` on
timeout. -/
private def awaitUntil {α : Type} (task : Task (Except IO.Error α)) (deadline : Nat) :
    IO (Option (Except IO.Error α)) := do
  repeat
    if ← IO.hasFinished task then return some task.get
    if (← IO.monoMsNow) > deadline then return none
    IO.sleep 5
  return none

/-- Run `cmd` with `args`, `stdin` on its standard input, within `limits`. The program is
started in its own session and process group. Its standard input is written and closed by a
task of its own (the program sees the end of its input), and its standard output and error are
read by tasks of their own, at the same time, to their end. While the program runs, the
deadline and the cancellation token `token?` are checked every 10 ms. Once the program has
exited, its process group is ended, so that descendants holding the pipes go too, and the
output is awaited for at most two more seconds. On every other exit path (timeout,
cancellation, error) the group is ended as well. Not covered: a descendant that leaves the group
(by calling `setsid` itself) and keeps a pipe open leaves its reader task blocked until it exits,
which the run does not wait for; a process in an uninterruptible wait may stay unreaped. -/
def runProgram (cmd : String) (args : Array String) (stdin : String := "")
    (limits : RunLimits := {}) (token? : Option IO.CancelToken := none) :
    IO (Except RunFailure RunResult) := do
  let deadline := (← IO.monoMsNow) + limits.timeoutMs
  let spawnArgs : IO.Process.SpawnArgs :=
    { cmd, args, stdin := .piped, stdout := .piped, stderr := .piped, setsid := true }
  let child ← try IO.Process.spawn spawnArgs
    catch error => return .error (.unavailable s!"cannot start '{cmd}': {error}")
  let (input, child) ← child.takeStdin
  let mut reaped := false
  try
    let writer ← IO.asTask (writeAll input stdin) .dedicated
    let output ← IO.asTask (readBounded child.stdout limits.maxOutputBytes) .dedicated
    let errors ← IO.asTask (readBounded child.stderr limits.maxErrorBytes) .dedicated
    let mut code : Option UInt32 := none
    repeat
      code ← child.tryWait
      if code.isSome then break
      if ← cancelled token? then return .error .cancelled
      if (← IO.monoMsNow) > deadline then return .error (.timeout limits.timeoutMs)
      IO.sleep 10
    reaped := true
    -- Descendants that still hold the pipes are ended with the group.
    terminateGroup child (reaped := true)
    discard <| awaitUntil writer ((← IO.monoMsNow) + 500)
    let grace := (← IO.monoMsNow) + 2000
    let (bytes, overflow) ← match ← awaitUntil output grace with
      | some (.ok result) => pure result
      | some (.error error) => return .error (.io (toString error))
      | none => return .error .unclosed
    let (errorBytes, stderrTruncated) ← match ← awaitUntil errors grace with
      | some (.ok result) => pure result
      | some (.error error) => return .error (.io (toString error))
      | none => return .error .unclosed
    if overflow then return .error (.overflow limits.maxOutputBytes)
    let some stdout := String.fromUTF8? bytes | return .error .notUTF8
    let stderr := (String.fromUTF8? errorBytes).getD ""
    let exitCode := code.getD 0
    -- Lean reports a program it cannot execute through the child's error stream.
    if exitCode != 0 && (stderr.splitOn "could not execute external process").length > 1 then
      return .error (.unavailable s!"cannot start '{cmd}': {stderr.trimAscii}")
    return .ok { exitCode, stdout, stderr, stderrTruncated }
  catch error =>
    return .error (.io (toString error))
  finally
    unless reaped do terminateGroup child

/-- Run `tool` (the program of its environment variable, else its default) with `args` and
`stdin`, within `limits`. -/
def ExternalTool.run (tool : ExternalTool) (args : Array String) (stdin : String := "")
    (limits : RunLimits := {}) (token? : Option IO.CancelToken := none) :
    IO (Except RunFailure RunResult) := do
  match ← runProgram (← tool.program) args stdin limits token? with
  | .error (.unavailable reason) =>
      return .error (.unavailable s!"{reason} (set {tool.envVar} to the {tool.name} program)")
  | result => return result

end DSLean
