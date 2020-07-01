open Types

let string_of_symbol : sexpr -> string = function
  | Symbol name -> name
  | _ -> failwith "not a symbol"

let initial_env : env = []

let rec eval (env : env) (e : sexpr) : sexpr =
    match e with
  | Atom(_) -> e
  | Special(_) -> e
  | Symbol(s) -> (List.assoc s env)
  | Call(l) -> (eval_call env l)

and is_special (es : sexpr list) : bool =
  match es with
    [] -> false
  | (Special _)::_ -> true
  | (Call head::tail) -> (is_special head) || (is_special tail)
  | _::tail -> (is_special tail)

and eval_call (env : env) (es : sexpr list) : sexpr =
  match es with
  | [Call(l)] -> (eval_call env l)
  | _ -> (if (is_special es) then (eval_special env es)
          else (apply env es))

and eval_special (env : env) (es : sexpr list) : sexpr =
  match es with
  | [Special If;e1;e2;e3] -> (match (eval env e1) with
        Atom(Bool(b)) -> (if b then (eval env e2)
                          else (eval env e3))
      | _ -> failwith "eval_special")
  | [Special Lambda;Call args;body] -> 
      Atom (Fun (env,(List.map (function Symbol name -> name | _ -> assert false) args,body)))
  | [Special Let;Call[name;e1];e2] -> 
      let es' = Call [Call [Special Lambda;Call [name];e2];e1] in 
      eval env es'
  | _ -> apply env es

and apply (env : env) (es : sexpr list) : sexpr =
  let es_eval = (List.map (eval env) es) in
  match es_eval with
  | Atom(Primitive(p))::tail -> (apply_primitive p tail)
  | Atom(Fun(e,c))::tail -> (apply_function (e,c) tail)
  | _::tail -> (apply env tail) 
  | [] -> failwith "apply"

and apply_function (vf : env * code) (args : sexpr list) : sexpr =
  let (envr,(xs,e)) = vf in
  if (List.length args <> List.length xs) then failwith "apply_function"
  else (let lenv = (extend_env envr xs args) in
        (eval lenv e))

and apply_primitive (p : primitive) (args : sexpr list) : sexpr =
  match p,args with
  | Add,[Atom (Int n);Atom (Int m)] -> Atom (Int (n + m))    (* PS: on pourrait aussi faire un (+) n-aire, avec fold_left *)
  | Sub,[Atom (Int n);Atom (Int m)] -> Atom (Int (n - m))
  | Mul,[Atom (Int n);Atom (Int m)] -> Atom (Int (n * m))
  | Div,[Atom (Int n);Atom (Int m)] -> Atom (Int (n / m))
  | Eq,[Atom (Int n);Atom (Int m)] -> Atom (Bool (n = m))
  | Lt,[Atom (Int n);Atom (Int m)] -> Atom (Bool (n < m))
  | _ -> failwith "apply_primitive"

and extend_env (env : env) (xs : string list) (vs : sexpr list)  : env = 
  let l = (List.combine xs vs) in
  l@env

let example_1 : string = "(+ 1 2)"

let sexpr_example_1 : sexpr =
  Call
    [ Atom (Primitive Add)
    ; Atom (Int 1)
    ; Atom (Int 2)
    ]

let example_2 : string = "(let (y (lambda (x) (+ x 10))) (y 2))"

let sexpr_example_2 : sexpr =
  Call
    [ Special Let
    ; Call
      [ Symbol "y"
      ; Call
        [ Special Lambda
        ; Call [ Symbol "x" ]
        ; Call
          [ Atom (Primitive Add)
          ; Symbol "x"
          ; Atom (Int 10)
          ]
        ]
      ]
    ; Call [ Symbol "y"; Atom (Int 2) ]
    ]

let example_3 : string = "((lambda (x) (let (a 10) (let (x 20) (+ x 1)))) 20000)"

let sexpr_example_3 : sexpr =
  Call
    [ Call
      [ Special Lambda
      ; Call [ Symbol "x" ]
      ; Call
        [ Special Let
        ; Call [ Symbol "a"; Atom (Int 10) ]
        ; Call
          [ Special Let
          ; Call [ Symbol "x"; Atom (Int 20) ]
          ; Call
            [ Atom (Primitive Add)
            ; Symbol "x"
            ; Atom (Int 1)
            ]
          ]
        ]
      ]
      ; Atom (Int 20000)
    ]

 let my_example_1 : string = "(/ 27 3)"

 let sexpr_my_example_1 : sexpr = 
  Call[
    Atom (Primitive Div);
    Atom (Int 27);
    Atom (Int 3)
  ]

let my_example_2 : string = "((lambda (x y) (* x y)) 10 26)"

let sexpr_my_example_2 : sexpr =
  Call[
    Call[
      Special Lambda;
      Call[
        Symbol "x"; Symbol "y"
      ];
      Call[
        Atom (Primitive Add);
        Symbol "x";
        Symbol "y"
      ]
    ];
   Atom (Int 10); Atom (Int 26)
  ]

let main () =
  print_string "example_1 : ";
  print_string example_1;
  print_string " = ";
  let prog = Parser.parse example_1 in
  let exprs = List.map (eval initial_env) prog in
  List.fold_left (fun _ x -> print_endline (Parser.string_of_sexpr x)) () exprs;
  
  print_string "example_2 : ";
  print_string example_2;
  print_string " = ";
  let prog2 = Parser.parse example_2 in
  let exprs2 = List.map (eval initial_env) prog2 in
  List.fold_left (fun _ x -> print_endline (Parser.string_of_sexpr x)) () exprs2;

  print_string "example_3 : ";
  print_string example_3;
  print_string " = ";
  let prog3 = Parser.parse example_3 in
  let exprs3 = List.map (eval initial_env) prog3 in
  List.fold_left (fun _ x -> print_endline (Parser.string_of_sexpr x)) () exprs3;

  print_string "my_example_1 : ";
  print_string my_example_1;
  print_string " = ";
  let prog4 = Parser.parse my_example_1 in
  let exprs4 = List.map (eval initial_env) prog4 in
  List.fold_left (fun _ x -> print_endline (Parser.string_of_sexpr x)) () exprs4;

  print_string "my_example_2 : ";
  print_string my_example_2;
  print_string " = ";
  let prog5 = Parser.parse my_example_2 in
  let exprs5 = List.map (eval initial_env) prog5 in
  List.fold_left (fun _ x -> print_endline (Parser.string_of_sexpr x)) () exprs5;
  ()

let () = main ();;
