(* utility function to catch errors from parsing and compilation *)
val with_error_reporting : Format.formatter -> 'a -> (unit -> 'a) -> 'a


