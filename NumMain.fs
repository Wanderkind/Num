module Num

let ( %% ) (a: int64) (b: int64) : int64 = (a % b + abs(b)) % (abs b)

let rec gcd (a: int64) (b: int64) : int64 =
    let p, q = abs a, abs b
    if q = 0L then p
    else gcd q (p %% q)

let squareExtract (x: int64) : int64 * int64 =
    let rec f a (factor: int64) (acc: int64) : int64 =
        if a = 1L then acc else
        let rec g (u: int64) (two: bool) (acc': int64) : int64 =
            if u %% factor > 0L then f u (factor + 1L) acc'
            else g (u/factor) (not two) (acc'*(if two then factor else 1L))
        g a false acc
    let k = f x 2L 1L
    (k, x/k/k)

type num =
| Zero
| Int of int64
| Sqt of int64 * num
| Frc of num * int64
| Add of num * num

let rec reducible (p: num) (q: num) : bool =
    match (p, q) with
    | (Zero, _) -> true
    | (_, Zero) -> true
    | (Int _, Int _) -> true
    | (Int _, Frc (Int _, _)) -> true
    | (Frc (Int _, _), Int _) -> true
    | (Frc (Int _, _), Frc (Int _, _)) -> true
    | (Sqt (_, b), Sqt (_, d)) -> b = d
    | (Sqt (_, b), Frc (Sqt (_, d), _)) -> b = d
    | (Frc (Sqt (_, b), _), Sqt (_, e)) -> b = e
    | (Frc (Sqt (_, b), _), Frc (Sqt (_, e), _)) -> b = e
    | (Add (a, b), _) -> reducible a q || reducible b q
    | (_, Add (a, b)) -> reducible a p || reducible b p
    | _ -> false

let rec sqrtFactor (x: num) : int64 =
    match x with
    | Zero -> 0L
    | Int _ -> 1L
    | Sqt _ ->
        let y = sqrtSanitize x
        match y with
        | Sqt (_, Int a) -> a
        | Sqt (_, _) -> 0L
        | _ -> sqrtFactor y
    | Frc _ ->
        let y = fracSanitize x
        match y with
        | Frc (Int _, _) -> 1L
        | Frc (Sqt (a, b), _) -> Sqt (a, b) |> sqrtFactor
        | Frc (a, _) -> sqrtFactor a
        | _ -> sqrtFactor y
    | Add _ ->
        let y = addSanitize x
        match y with
        | Add (_, _) -> 0L
        | _ -> sqrtFactor y

and intmul (x: int64) (y: num) : num =
    if x = 0L then Zero else
    match y with
    | Zero -> Zero
    | Int 0L -> Zero
    | Int a -> Int (x*a)
    | Sqt (a, b) -> Sqt (x*a, b) |> sqrtSanitize
    | Frc (a, b) -> Frc (intmul x a, b) |> fracSanitize
    | Add (a, b) -> add (intmul x a) (intmul x b)

and fracSanitize (x: num) : num =
    match x with
    | Frc (p, q) ->
        match (q: int64) with
        | 0L -> failwith "#### module Num: Frc (_, 0) generated. ####"
        | 1L -> p
        | _ ->
            if q < 0L then Frc (intmul -1L p, -q) |> fracSanitize else
            match (p: num) with
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

and reduce (lst: num list) : num list =
    let rec inner (acc: num list) = function
    | [] -> acc
    | h :: t ->
        let rec f (prot: num) (save: num list) = function
        | [] -> inner (prot :: acc) save
        | h' :: t' ->
            if reducible prot h' then f (add prot h' |> addSanitize) save t'
            else f prot (h' :: save) t'
        f h [] t
    inner [] lst |> List.sortBy sqrtFactor

and addSanitize (y: num) : num =
    let rec g (x: num) : num list =
        match x with
        | Add (p, q) -> g p @ g q
        | _ -> [x]
    let redlst = g y |> reduce
    let rec maketree (acc: num) = function
    | [] -> acc
    | h :: t ->
        match (t: num list) with
        | [] -> Add (h, acc)
        | _ -> maketree (Add (h, acc)) t
    maketree (List.head redlst) (List.tail redlst)

and add (x: num) (y: num) : num =
    match (x, y) with
    | (Zero, _) -> y
    | (_, Zero) -> x
    | (Int a, Int b) -> if a + b = 0L then Zero else Int (a + b)
    | (Int _, Sqt _) -> Add (x, y)
    | (Int a, Frc (b, c)) -> if reducible x b then Frc (add (Int (a*c)) b, c) |> fracSanitize else Add (x, y)
    | (Sqt _, Int _) -> Add (x, y)
    | (Sqt (a, b), Sqt (c, d)) -> if b <> d then Add (x, y) else if a + c = 0L then Zero else Sqt ((a + c), b) |> sqrtSanitize
    | (Sqt (a, b), Frc (c, d)) -> if reducible x c then Frc (add (Sqt (a*d, b)) c, d) |> fracSanitize else Add (x, y)
    | (Frc (a, b), Int c) -> if reducible a y then Frc (add (Int (c*b)) a, b) |> fracSanitize else Add (x, y)
    | (Frc (a, b), Sqt (c, d)) -> if reducible a y then Frc (add (Sqt (c*b, d)) a, b) |> fracSanitize else Add (x, y)
    | (Frc (a, b), Frc (c, d)) -> if reducible a c then Frc (add (intmul d a) (intmul b c) |> addSanitize, b*d) |> fracSanitize else Add (x, y)
    | _ -> Add (x, y) |> addSanitize

and sqrtSanitize (x: num) : num =
    match x with
    | Sqt (a, b) ->
        if negative b then failwith "#### module Num: Domain error in sqrt. ####"
        match (a: int64) with
        | 0L -> Zero
        | _ ->
            match (b: num) with
            | Zero -> Zero
            | Int 0L -> Zero
            | Int n ->
                match squareExtract n with
                | (1L, _) -> x
                | (c, 1L) -> Int (c*a)
                | (c, d) -> Sqt (c*a, Int d) |> sqrtSanitize
            | Sqt (p, q) ->
                match squareExtract p with
                | (1L, _) -> x
                | (c, d) -> Sqt (c*a, Sqt (d, q) |> sqrtSanitize) |> sqrtSanitize
            | Frc (p, q) -> Frc ((Sqt (a, intmul q p) |> sqrtSanitize), q) |> fracSanitize
            | Add (p, q) ->
                if reducible p q then Sqt (a, add p q |> addSanitize) |> sqrtSanitize
                else
                    match (p, q) with
                    | (Int c, Sqt (d, Int e)) ->
                        if d %% 2L = 1L then x else
                        let k = d/2L
                        let rec f (u: int64) (v: int64) : int64 * int64 =
                            if u*v = k*k*e || u < 0L then (u, v)
                            else f (u - k) (v + k)
                        let u, v = f (c/2L) (c - c/2L)
                        if u < 0L then x else
                        Add (Sqt ((if c*d > 0L then 1L else -1L), Int u) |> sqrtSanitize, Sqt (1L, Int v) |> sqrtSanitize) |> addSanitize
                    | _ -> x // WIP
    | _ -> x

and mul (x: num) (y: num) : num =
    match (x, y) with
    | (Zero, _) -> Zero
    | (_, Zero) -> Zero
    | (Int a, Int b) -> Int (a*b)
    | (Int a, Sqt (b, c)) -> Sqt (a*b, c)
    | (Int a, Frc (b, c)) -> Frc (intmul a b, c) |> fracSanitize
    | (Sqt (a, b), Int c) -> Sqt (a*c, b)
    | (Sqt (a, b), Sqt (c, d)) -> Sqt (a*c, mul b d) |> sqrtSanitize
    | (Sqt _, Frc (c, d)) -> Frc (mul x c, d) |> fracSanitize
    | (Frc (a, b), Int c) -> Frc (intmul c a, b) |> fracSanitize
    | (Frc (a, b), Sqt _) -> Frc (mul y a, b) |> fracSanitize
    | (Frc (a, b), Frc (c, d)) -> Frc (mul a c, b*d) |> fracSanitize
    | (Add (a, b), _) -> Add (mul a y, mul b y) |> addSanitize
    | (_, Add (a, b)) -> Add (mul a x, mul b x) |> addSanitize

and square (x: num) : num =
    match x with
    | Zero -> Zero
    | Int a -> Int (a*a)
    | Sqt (a, b) -> intmul (a*a) b
    | Frc (a, b) -> Frc (square a, b*b) |> fracSanitize
    | Add (a, b) -> mul a b |> intmul 2L |> add (square a) |> add (square b) |> addSanitize

and isZero (x: num) : bool =
    match x with
    | Zero -> true
    | Int a -> a = 0L
    | Sqt (a, b) -> a = 0L || isZero b
    | Frc (a, _) -> isZero a
    | Add (a, b) -> intmul -1 a |> ( *= ) b

and ( *= ) (x: num) (y: num) : bool =
    match (x, y) with
    | (Zero, _) -> isZero y
    | (Int u, Int v) -> u = v
    | (Int _, Sqt (_, _)) ->
        let v = sqrtSanitize y
        match v with
        | Sqt (_, _) -> false
        | _ -> x *= v
    | (Int _, Frc (_, _)) ->
        let v = fracSanitize y
        match v with
        | Frc (_, _) -> false
        | _ -> x *= v
    | (Int _, Add (_, _)) ->
        let v = addSanitize y
        match v with
        | Frc (_, _) -> false
        | _ -> x *= v
    | (Sqt (_, _), Sqt (_, _)) ->
        let u, v = sqrtSanitize x, sqrtSanitize y
        match (u, v) with
        | (Sqt (a, b), Sqt (c, d)) -> a = c && b = d
        | (_, Sqt (_, _)) | (Sqt (_, _), _) -> false
        | (_, _) -> u *= v
    | (Sqt (_, _), Frc (_, _)) ->
        let u, v = sqrtSanitize x, fracSanitize y
        match (u, v) with
        | (Sqt (_, _), Frc (_, _)) -> false
        | (_, _) -> u *= v
    | (Sqt (_, _), Add (_, _)) ->
        let u, v = sqrtSanitize x, addSanitize y
        match (u, v) with
        | (Sqt (_, _), Add (_, _)) -> false
        | (_, _) -> u *= v
    | (Frc (_, _), Frc (_, _)) ->
        let u, v = fracSanitize x, fracSanitize y
        match (u, v) with
        | (Frc (a, b), Frc (c, d)) -> a = c && b = d
        | (_, Frc (_, _)) | (Frc (_, _), _) -> false
        | (_, _) -> u *= v
    | (Frc (_, _), Add (_, _)) ->
        let u, v = fracSanitize x, addSanitize y
        match (u, v) with
        | (Frc (_, _), Add (_, _)) -> false
        | (_, _) -> u *= v
    | (Add (_, _), Add (_, _)) ->
        let u, v = addSanitize x, addSanitize y
        match (u, v) with
        | (Add (a, b), Add (c, d)) -> (a = c && b = d) || (a = d && b = c)
        | (_, Add (_, _)) | (Add (_, _), _) -> false
        | (_, _) -> u *= v
    | _ -> y *= x // reduced for the sake of size, costs maybe an extra stack?

and ( *> ) (x: num) (y: num) : bool =
    if x *= y then false else
    match (x, y) with
    | (Zero, _) -> negative y
    | (_, Add (b, c)) ->
        if reducible x b then (intmul -1 b |> add x) *> c
        else if reducible x c then (intmul -1 c |> add x) *> b
        else
            let d = intmul -1 b |> add x
            let nd, nc = negative d, negative c
            if nd <> nc then nc
            else if nd then square c *> square d
            else square d *> square c
    | (Int a, Int b) -> a > b
    | (Int a, Sqt (b, c)) ->
        if negative c then failwith "#### module Num: Domain error in sqrt. ####" else
        let ay = intmul a y
        if negative ay then b < 0L
        else if a > 0L then square x *> square y
        else square y *> square x
    | (Int a, Frc (b, c)) ->
        if c = 0L then failwith "#### module Num: Denominator 0L detected during comparison. ####"
        else (Int (a*c) *> b) = (c > 0L)
    | (Sqt (a, b), Sqt (c, d)) ->
        if negative b || negative d then failwith "#### module Num: Domain error in sqrt. ####" else
        let na, nc = a < 0L, c < 0L
        if na <> nc then nc
        else if na then square y *> square x
        else square x *> square y
    | (Sqt (a, b), Frc (c, d)) ->
        if d = 0L then failwith "#### module Num: Denominator 0L detected during comparison. ####"
        else (Sqt (a*d, b) *> c) = (d > 0L)
    | (Frc(a, b), Frc (c, d)) ->
        if b = 0L || d = 0L then failwith "#### module Num: Denominator 0L detected during comparison. ####" else
        let nx, ny = negative x, negative y
        if nx <> ny then ny else
            let xx, yy = intmul d a, intmul b c
            if (b < 0L) = (d < 0L) then xx *> yy
            else yy *> xx
    | _ -> y *> x // reduced for the sake of size, costs maybe an extra stack?

and ( *< ) (x: num) (y: num) : bool = y *> x

and negative (x: num) : bool =
    match x with
    | Zero -> false
    | Int a -> a < 0L
    | Sqt (a, _) -> a < 0L
    | Frc (a, b) -> negative a <> (b < 0L)
    | Add (a, b) ->
        let c, d = square a, square b
        match (negative a, negative b) with
        | (true, false) -> c *> d
        | (false, true) -> c *< d
        | (x, _) -> x

let rec div (x: num) (y: num) : num =
    match y with
    | Zero -> failwith "#### module Num: Division by Zero attempted. ####"
    | Int 0L -> failwith "#### module Num: Division by Int 0 attempted. ####"
    | Int a -> Frc (x, a) |> fracSanitize
    | Sqt (a, b) -> div (mul x (Sqt (1L, b))) (intmul a b)
    | Frc (a, b) -> div (intmul b x) a |> fracSanitize
    | Add (a, b) -> div (intmul -1L b |> add a |> addSanitize) (square b |> intmul -1L |> add (square a) |> addSanitize) |> fracSanitize |> mul x

let rec sqrt (x: num) : num =
    if negative x then failwith "#### module Num: Domain error in sqrt. ####" else
    match x with
    | Zero -> Zero
    | Int 0L -> Zero
    | Int a -> let p, q = squareExtract a in Sqt (p, Int q)
    | Sqt (a, b) -> let p, q = squareExtract a in Sqt (p, Sqt (q, b)) |> sqrtSanitize
    | Frc (a, b) -> Frc (Sqt (1, intmul b a) |> sqrtSanitize, b) |> fracSanitize
    | _ -> Sqt (1L, x) |> sqrtSanitize

let listsum (lst: num list) : num =
    let rec f (acc: num) = function
    | [] -> acc
    | h :: t -> f (add acc h) t
    f Zero lst