open Base

type t =
  | Name of string
  | App of t * t
