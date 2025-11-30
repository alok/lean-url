import LeanUrl.Url.Basic

open LeanUrl

/-- info: false -/
#guard_msgs in
#eval
  let empty : Url := Inhabited.default
  empty.hasCredentials

/-- info: false -/
#guard_msgs in
#eval
  let empty : Url := { (Inhabited.default : Url) with password := "" }
  empty.hasCredentials

/-- info: false -/
#guard_msgs in
#eval
  let empty : Url := { (Inhabited.default : Url) with username := "" }
  empty.hasCredentials

/-- info: false -/
#guard_msgs in
#eval
  let empty : Url := { (Inhabited.default : Url) with password := "", username := "" }
  empty.hasCredentials

/-- info: true -/
#guard_msgs in
#eval
  let empty : Url := { (Inhabited.default : Url) with password := " ", username := "x" }
  empty.hasCredentials

/-- info: true -/
#guard_msgs in
#eval
  let empty : Url := { (Inhabited.default : Url) with password := "x" }
  empty.hasCredentials

/-- info: true -/
#guard_msgs in
#eval
  let empty : Url := { (Inhabited.default : Url) with username := "x" }
  empty.hasCredentials
