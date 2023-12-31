module Num

let ( %% ) a b = (a % b + b) % b

let rec gcd (a: int) (b: int) =
    if b = 0 then a
    else gcd b (a %% b)

type num =
| Zero
| Int of int
| Sqt of int * num
| Frc of num * int
| Add of num * num

let reducible (p: num) (q: num) =
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
    | _ -> false

let rec intmul (x: int) (y: num) =
    if x = 0 then Zero else
    match y with
    | Zero -> Zero
    | Int 0 -> Zero
    | Int a -> Int (x*a)
    | Sqt (a, b) -> Sqt (x*a, b) |> sqrtsan
    | Frc (a, b) -> Frc (intmul x a, b) |> fracsan
    | Add (a, b) -> add (intmul x a) (intmul x b)

and fracsan (x: num) =
    match x with
    | Frc (p, q) ->
        match q with
        | 1 -> p
        | _ ->
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
            | Frc (a, b) -> Frc (a, b*q) |> fracsan
            | Add (a, b) -> add (Frc (a, q) |> fracsan) (Frc (b, q) |> fracsan)
    | _ -> failwith "#### Wrong param type in fracsan. ####"

and addsan (y: num) =
    let rec reduce acc = function
    | [] -> acc
    | h :: t ->
        let rec f prot save = function
        | [] -> reduce (prot :: acc) save
        | h' :: t' ->
            if reducible prot h' then f (add prot h') save t'
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
        | h' :: t' -> maketree (Add (h, acc)) t
    maketree (List.head redlst) (List.tail redlst)

and add (x: num) (y: num) =
    match (x, y) with
    | (Zero, _) -> y
    | (_, Zero) -> x
    | (Int a, Int b) -> if a + b = 0 then Zero else Int (a + b)
    | (Int a, Sqt (b, c)) -> Add (x, y)
    | (Int a, Frc (b, c)) -> Frc (add (Int (a*c)) b, c) |> fracsan
    | (Sqt (a, b), Int c) -> Add (x, y)
    | (Sqt (a, b), Sqt (c, d)) -> if b <> d then Add (x, y) else if a + c = 0 then Zero else Sqt((a + c), b)
    | (Sqt (a, b), Frc (c, d)) -> Frc (add (Sqt (a*d, b)) c, d) |> fracsan
    | (Frc (a, b), Int c) -> Frc (add (Int (c*b)) a, b) |> fracsan
    | (Frc (a, b), Sqt (c, d)) -> Frc (add (Sqt (c*b, d)) a, b) |> fracsan
    | (Frc (a, b), Frc (c, d)) -> if reducible a c then Frc (add (intmul d a) (intmul b c), b*d) |> fracsan else Add (x, y)
    | _ -> Add (x, y) |> addsan

and squareExtract (x: int) =
    let rec f a factor acc =
        if a = 1 then acc else
        let rec g u two acc' =
            if u %% factor > 0 then f u (factor + 1) acc'
            else g (u/factor) (not two) (acc'*(if two then factor else 1))
        g a false acc
    let k = f x 2 1
    (k, x/k/k)

and sqrtsan (x: num) =
    match x with
    | Sqt (a, b) ->
        match b with
        | Zero -> Zero
        | Int 0 -> Zero
        | Int n ->
            match squareExtract n with
            | (1, d) -> x
            | (c, 1) -> Int (c*a)
            | (c, d) -> Sqt (c*a, Int d)
        | Frc (p, q) -> Frc ((Sqt (a, intmul q p) |> sqrtsan), q) |> fracsan
        | _ -> x
    | Zero -> Zero
    | _ -> failwith "#### Wrong param type in sqrtsan. ####"

let rec mul (x: num) (y: num) =
    match (x, y) with
    | (Zero, _) -> Zero
    | (_, Zero) -> Zero
    | (Int a, Int b) -> Int (a*b)
    | (Int a, Sqt (b, c)) -> Sqt (a*b, c)
    | (Int a, Frc (b, c)) -> Frc (intmul a b, c) |> fracsan
    | (Sqt (a, b), Int c) -> Sqt (a*c, b)
    | (Sqt (a, b), Sqt (c, d)) -> Sqt (a*c, mul b d) |> sqrtsan
    | (Sqt (a, b), Frc (c, d)) -> Frc (mul x c, d) |> fracsan
    | (Frc (a, b), Int c) -> Frc (intmul c a, b) |> fracsan
    | (Frc (a, b), Sqt (c, d)) -> Frc (mul y a, b) |> fracsan
    | (Frc (a, b), Frc (c, d)) -> Frc (mul a c, b*d) |> fracsan
    | _ -> Add (x, y) |> addsan

let rec div (x: num) (y: num) =
    match y with
    | Zero -> failwith "#### Division by Zero attempted. ####"
    | Int 0 -> failwith "#### Division by Int 0 attempted. ####"
    | Int b -> Frc (x, b) |> fracsan
    | Sqt (b, c) -> div (mul x (Sqt (1, c))) (intmul b c)
    | Frc (Int b, c) -> Frc (intmul c x, b) |> fracsan
    | Frc (Sqt (b, c), d) -> div (mul x (Sqt (d, c))) (intmul b c)
    | Frc (Frc (b, c), d) -> div (mul x (Int (c*d))) b
    | _ -> failwith "#### Unusual divisor type ####"

let sqrt (x: num) =
    match x with
    | Int a -> let p, q = squareExtract a in Sqt (p, Int q)
    | Sqt (a, b) -> let p, q = squareExtract a in Sqt (p, Sqt(q, b)) |> sqrtsan
    | Frc (a, b) -> Frc ((Sqt (1, intmul b a)) |> sqrtsan, b) |> fracsan
    | _ -> x

let listsum lst =
    let rec f acc = function
    | [] -> acc
    | h :: t -> f (add acc h) t
    f (Zero) lst
