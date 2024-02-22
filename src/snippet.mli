val fix_snippet : string -> string
val add_snippet : string -> string -> unit
val add_header_snippet : string -> string -> unit
val command_snippet : string -> string -> unit
val command_header_snippet : string -> string -> unit
val command_rawsnippet : string -> string -> unit
val command_header_rawsnippet : string -> string -> unit
val add_thunk : string -> (unit -> string) -> unit
val add_header_thunk : string -> (unit -> string) -> unit
