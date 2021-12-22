type severity = SevError | SevFatal | SevBug

exception Excp of severity * string

let exc_not_supported = Excp (SevError, "Not supported yet")

let exc_should_not_happen = Excp (SevFatal, "Should not happen!")
