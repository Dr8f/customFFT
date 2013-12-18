open Lib
;;

type code =
  Class of string (* name *)
| Chain of code list
;;

let code_of_lib (lib : lib) : code = 
  Chain ([
    Class "RS";
    Class "RS2";
  ]);
;;

