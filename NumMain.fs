module Num

let ( %% ) (a: int) (b: int) = (a % b + b) % b

let rec gcd (a: int) (b: int) =
    if b = 0 then a
    else gcd b (a %% b)

let squareExtract (x: int) =
    let rec f a factor acc =
        if a = 1 then acc else
        let rec g u two acc' =
            if u %% factor > 0 then f u (factor + 1) acc'
            else g (u/factor) (not two) (acc'*(if two then factor else 1))
        g a false acc
    let k = f x 2 1
    (k, x/k/k)

type num =
| Zero
| Int of int
| Sqt of int * num
| Frc of num * int
| Add of num * num

let rec reducible (p: num) (q: num) =
    match (p, q) with
    | (Zero, _) -> true
    | (_, Zero) -> true
    | (Int a, Int b) -> true
    | (Int a, Frc (Int b, c)) -> true
    | (Frc (Int a, b), Int c) -> true
    | (Frc (Int a, b), Frc (Int c, d)) -> true
    | (Sqt (a, b), Sqt (c, d)) -> b = d
    | (Sqt (a, b), Frc (Sqt (c, d), e)) -> b = d
    | (Frc (Sqt (a, b), c), Sqt (d, e)) -> b = e
    | (Frc (Sqt (a, b), c), Frc (Sqt (d, e), f)) -> b = e
    | (Add (a, b), _) -> reducible a q || reducible b q
    | (_, Add (a, b)) -> reducible a p || reducible b p
    | _ -> false

let rec intmul (x: int) (y: num) =
    if x = 0 then Zero else
    match y with
    | Zero -> Zero
    | Int 0 -> Zero
    | Int a -> Int (x*a)
    | Sqt (a, b) -> Sqt (x*a, b) |> sqrtSanitize
    | Frc (a, b) -> Frc (intmul x a, b) |> fracSanitize
    | Add (a, b) -> add (intmul x a) (intmul x b)

and fracSanitize (x: num) =
    match x with
    | Frc (p, q) ->
        match q with
        | 0 -> failwith "#### Frc (_, 0) generated. ####"
        | 1 -> p
        | _ ->
            if q < 0 then Frc (intmul -1 p, -q) |> fracSanitize else
            match p with
            | Zero -> Zero
            | Int a ->
                let g = gcd a q
                if g = q then Int (a/g)
                else Frc (Int (a/g), q/g)
            | Sqt (a, b) ->
                let g = gcd a q
                if g = q then Sqt (a/g, b)
                else Frc (Sqt (a/g, b), q/g)
            | Frc (a, b) -> Frc (a, b*q) |> fracSanitize
            | Add (a, b) -> add (Frc (a, q) |> fracSanitize) (Frc (b, q) |> fracSanitize) |> addSanitize
    | _ -> x

and addSanitize (y: num) =
    let rec reduce acc = function
    | [] -> acc
    | h :: t ->
        let rec f prot save = function
        | [] -> reduce (prot :: acc) save
        | h' :: t' ->
            if reducible prot h' then f (add prot h' |> addSanitize) save t'
            else f prot (h' :: save) t'
        in f h [] t
    let rec g x =
        match x with
        | Add (p, q) -> g p @ g q
        | _ -> [x]
    let redlst = g y |> reduce []
    let rec maketree acc = function
    | [] -> acc
    | h :: t ->
        match t with
        | [] -> Add (h, acc)
        | _ -> maketree (Add (h, acc)) t
    maketree (List.head redlst) (List.tail redlst)

and add (x: num) (y: num) =
    match (x, y) with
    | (Zero, _) -> y
    | (_, Zero) -> x
    | (Int a, Int b) -> if a + b = 0 then Zero else Int (a + b)
    | (Int a, Sqt (b, c)) -> Add (x, y)
    | (Int a, Frc (b, c)) -> Frc (add (Int (a*c)) b, c) |> fracSanitize
    | (Sqt (a, b), Int c) -> Add (x, y)
    | (Sqt (a, b), Sqt (c, d)) -> if b <> d then Add (x, y) else if a + c = 0 then Zero else Sqt((a + c), b) |> sqrtSanitize
    | (Sqt (a, b), Frc (c, d)) -> Frc (add (Sqt (a*d, b)) c, d) |> fracSanitize
    | (Frc (a, b), Int c) -> Frc (add (Int (c*b)) a, b) |> fracSanitize
    | (Frc (a, b), Sqt (c, d)) -> Frc (add (Sqt (c*b, d)) a, b) |> fracSanitize
    | (Frc (a, b), Frc (c, d)) -> if reducible a c then Frc (add (intmul d a) (intmul b c) |> addSanitize, b*d) |> fracSanitize else Add (x, y)
    | _ -> Add (x, y) |> addSanitize

and sqrtSanitize (x: num) =
    match x with
    | Zero -> Zero
    | Sqt (a, b) ->
        match a with
        | 0 -> Zero
        | _ ->
            match b with
            | Zero -> Zero
            | Int 0 -> Zero
            | Int n ->
                match squareExtract n with
                | (1, d) -> x
                | (c, 1) -> Int (c*a)
                | (c, d) -> Sqt (c*a, Int d) |> sqrtSanitize
            | Sqt (p, q) ->
                match squareExtract p with
                | (1, d) -> x
                | (c, d) -> Sqt (c*a, Sqt (d, q) |> sqrtSanitize) |> sqrtSanitize
            | Frc (p, q) -> Frc ((Sqt (a, intmul q p) |> sqrtSanitize), q) |> fracSanitize
            | Add (p, q) ->
                if reducible p q then Sqt (a, add p q |> addSanitize) |> sqrtSanitize
                else
                    match (p, q) with
                    | (Int c, Sqt (d, Int e)) ->
                        if d %% 2 = 1 then x else
                        let k = d/2
                        let rec f u v =
                            if u*v = k*k*e || u < 0 then (u, v)
                            else f (u - k) (v + k)
                        let u, v = f (c/2) (c - c/2)
                        if u < 0 then x else
                        Add (Sqt ((if c*d > 0 then 1 else -1), Int u) |> sqrtSanitize, Sqt (1, Int v) |> sqrtSanitize) |> addSanitize
                    | _ -> x (* WIP *)
    | _ -> x

let rec mul (x: num) (y: num) =
    match (x, y) with
    | (Zero, _) -> Zero
    | (_, Zero) -> Zero
    | (Int a, Int b) -> Int (a*b)
    | (Int a, Sqt (b, c)) -> Sqt (a*b, c)
    | (Int a, Frc (b, c)) -> Frc (intmul a b, c) |> fracSanitize
    | (Sqt (a, b), Int c) -> Sqt (a*c, b)
    | (Sqt (a, b), Sqt (c, d)) -> Sqt (a*c, mul b d) |> sqrtSanitize
    | (Sqt (a, b), Frc (c, d)) -> Frc (mul x c, d) |> fracSanitize
    | (Frc (a, b), Int c) -> Frc (intmul c a, b) |> fracSanitize
    | (Frc (a, b), Sqt (c, d)) -> Frc (mul y a, b) |> fracSanitize
    | (Frc (a, b), Frc (c, d)) -> Frc (mul a c, b*d) |> fracSanitize
    | (Add (a, b), _) -> Add (mul a y, mul b y) |> addSanitize
    | (_, Add (a, b)) -> Add (mul a x, mul b x) |> addSanitize

let rec square (x: num) =
    match x with
    | Zero -> Zero
    | Int a -> Int (a*a)
    | Sqt (a, b) -> intmul (a*a) b
    | Frc (a, b) -> Frc (square a, b*b) |> fracSanitize
    | Add (a, b) -> mul a b |> intmul 2 |> add (add (square a) (square b)) |> addSanitize

let rec div (x: num) (y: num) =
    match y with
    | Zero -> failwith "#### Division by Zero attempted. ####"
    | Int 0 -> failwith "#### Division by Int 0 attempted. ####"
    | Int a -> Frc (x, a) |> fracSanitize
    | Sqt (a, b) -> div (mul x (Sqt (1, b))) (intmul a b)
    | Frc (a, b) -> div (intmul b x) a |> fracSanitize
    | Add (a, b) -> div (intmul -1 b |> add a |> addSanitize) (square b |> intmul -1 |> add (square a) |> addSanitize) |> fracSanitize

let rec negative (x: num) =
    match x with
    | Zero -> false
    | Int a -> a < 0
    | Sqt (a, b) -> a < 0
    | Frc (a, b) -> negative a <> (b < 0)
    | Add (a, b) ->
        let c, d = square a, square b
        match (negative a, negative b) with
        | (true, false) -> c > d
        | (false, true) -> c < d
        | (x, y) -> x

let rec sqrt (x: num) =
    if negative x then failwith "#### Negative value in sqrt. ####" else
    match x with
    | Zero -> Zero
    | Int 0 -> Zero
    | Int a -> let p, q = squareExtract a in Sqt (p, Int q)
    | Sqt (a, b) -> let p, q = squareExtract a in Sqt (p, Sqt (q, b)) |> sqrtSanitize
    | Frc (a, b) -> Frc (Sqt (1, intmul b a) |> sqrtSanitize, b) |> fracSanitize
    | _ -> Sqt (1, x) |> sqrtSanitize

let listsum (lst: num list) =
    let rec f acc = function
    | [] -> acc
    | h :: t -> f (add acc h) t
    f Zero lst
