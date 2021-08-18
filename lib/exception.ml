type severity = SevError | SevFatal | SevBug

exception Excp of severity * string
