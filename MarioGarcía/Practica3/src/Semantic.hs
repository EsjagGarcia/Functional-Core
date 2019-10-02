module Semantic where

import Sintax

----------------------------- Semántica dinámica. ------------------------------

{--
   beta:

   Implementación textual de una alpha reducción.
-}
beta :: Expr -> Expr
beta (App (Fn x e) s) = subst e (x,s)
beta _ = error "Imposible beta reduction."

{--
   normal:

   Va a determinar si una expresión esta bloqueada, es decir no se puede reducir.
-}
normal :: Expr -> Bool
normal (V x) = True
normal (I n) = True
normal (B b) = True
normal (Fn x e) = normal e
normal (App e1 e2) = case e1 of
                          (Fn x e) -> False
                          _ -> (normal e1) && (normal e2)
normal _ = False

{--
    Función eval1:

    La función implementa la definición de un paso de ejecución para las expre-
    siones del lenguaje Aritmético-Booleanas.
-}

eval1 :: Expr -> Expr

eval1 (V x) = error "Have a free variable in the evaluation."
eval1 (I n) = error "Error in the parameters"
eval1 (B b) = error "Error in the parameters"

eval1 (Add (I n) (I m)) = I (n + m)
eval1 (Add (I n) e2) = Add (I n) (eval1 e2)
eval1 (Add e1 e2) = Add (eval1 e1) e2

eval1 (Mul (I n) (I m)) = I (n * m)
eval1 (Mul (I n) e2) = Mul (I n) (eval1 e2)
eval1 (Mul e1 e2) = Mul (eval1 e1) e2

eval1 (Succ (I n)) = I (n+1)
eval1 (Succ e) = Succ (eval1 e)

eval1 (Pred (I n)) = I (n-1)
eval1 (Pred e) = Pred (eval1 e)

eval1 (And (B b1) (B b2)) = B (b1 && b2)
eval1 (And (B b1) e2) = And (B b1) (eval1 e2)
eval1 (And e1 e2) = And (eval1 e1) e2

eval1 (Or (B b1) (B b2)) = B (b1 || b2)
eval1 (Or (B b1) e2) = Or (B b1) (eval1 e2)
eval1 (Or e1 e2) = Or (eval1 e1) e2

eval1 (Not (B b)) = B (not b)
eval1 (Not e) = Not (eval1 e)

eval1 (Lt (I n) (I m)) = B (n < m)
eval1 (Lt (I n) e2) = Lt (I n) (eval1 e2)
eval1 (Lt e1 e2) = Lt (eval1 e1) e2

eval1 (Gt (I n) (I m)) = B (n > m)
eval1 (Gt (I n) e2) = Gt (I n) (eval1 e2)
eval1 (Gt e1 e2) = Gt (eval1 e1) e2

eval1 (Eq (I n) (I m)) = B (n == m)
eval1 (Eq (I n) e2) = Eq (I n) (eval1 e2)
eval1 (Eq e1 e2) = Eq (eval1 e1) e2

eval1 (If (B b) e1 e2) = if b
                         then e1
                         else e2
eval1 (If e e1 e2) = If (eval1 e) e1 e2

eval1 (Let x e1 e2) = subst e2 (x, e1)

eval1 (App e1@(Fn x e) e2) = if (normal e2)
                             then subst e (x,e2)
                             else App e1 (eval1 e2)
eval1 (App e1 e2) = if (normal e1)
                    then App e1 (eval1 e2)
                    else App (eval1 e1) e2

eval1 (Fn x e) = Fn x (eval1 e)

{--
    isBloqued:

    Determina sí un estado está bloqueado, esto ocurre cuando no sé puede seguir
    evaluando la expresión.
-}

locked :: Expr -> Bool
locked (I n) = True
locked (B b) = True
locked (V x) = True
locked (Add (I n) (I m)) = False
--locked (Add (B b) _) = True
locked (Add e1 e2) = locked e1 || locked e2
locked (Mul (I n) (I m)) = False
--locked (Mul (B b) _) = True
locked (Mul e1 e2) = locked e1 || locked e2
locked (Succ (I n)) = False
locked (Succ e) = locked e
locked (Pred (I n)) = False
locked (Pred e) = locked e
locked (And (B b1) (B b2)) = False
locked (And e1 e2) = locked e1 || locked e1
locked (Or (B b1) (B b2)) = False
locked (Or e1 e2) = locked e1 || locked e2
locked (Not (B b)) = False
locked (Not e) = locked e
locked (Lt (I n) (I m)) = False
locked (Lt e1 e2) = locked e1 || locked e2
locked (Gt (I n) (I m)) = False
locked (Gt e1 e2) = locked e1 || locked e2
locked (Eq (I n) (I m)) = False
locked (Eq e1 e2) = locked e1 || locked e2
locked (If (B b) e1 e2) = False
locked (If e e1 e2) = locked e
locked (Let x e1 e2) = False
locked (App (Fn x e) e2) = False
locked (App e1 e2) = locked e1 || locked e2
locked (Fn x e) = locked e

{--
    Función evals:

    La función implementa la cerradura, devolviendo la evaluación de la expre-
    sión de entrada hasta un estado bloqueado, sin importar si este es inicial o
    final.
-}

evals :: Expr -> Expr
evals e = if locked e
          then e
          else evals(eval1(e))

{--
    isFinal:

    El programa decide si un estado es final. Esto es si y solo si dicho estado
    esta bloqueado y es un valor.
-}

final :: Expr -> Bool
final (I n) = True
final (B b) = True
final (Add _ _) = error "[Add] Expects two integer values as arguments."
final (Mul _ _) = error "[Mul] Expects two integer values as arguments."
final (Succ _) = error "[Succ] Expects an integer value as argument."
final (Pred _) = error "[Pred] Expects an integer value as argument."
final (And _ _) = error "[And] Expects two boolean values as arguments."
final (Or _ _) = error "[Or] Expects two boolean values as arguments."
final (Not _) = error "[Not] Expects an boolean value as argument."
final (Lt _ _) = error "[Lt] Expects two integer values as arguments."
final (Gt _ _) = error "[Gt] Expects two integer values as arguments."
final (Eq _ _) = error "[Eq] Expects two integer values as arguments."
final (If _ _ _) = error "[If] Expects a boolean value as argument to decide a expression."
--final (App _ _ _) = error "[App] Expect a Function as first argument."
final _ = False

{--
    evale:

    Evalua una expresión hasta llegar a un estado final, de no ocurrir esto, sig-
    nifica que ha ocurrido un error de ejecución, en cuyo caso, devolvemos dicho
    error.
-}
evale :: Expr -> Expr
evale expr = case (evals expr) of
            (I n) -> I n
            (B b) -> B b
            (Add _ _) -> error "[Add] Expects two integer values as arguments."
            (Mul _ _) -> error "[Mul] Expects two integer values as arguments."
            (Succ _) -> error "[Succ] Expects an integer value as argument."
            (Pred _) -> error "[Pred] Expects an integer value as argument."
            (And _ _) -> error "[And] Expects two boolean values as arguments."
            (Or _ _) -> error "[Or] Expects two boolean values as arguments."
            (Not _) -> error "[Not] Expects an boolean value as argument."
            (Lt _ _) -> error "[Lt] Expects two integer values as arguments."
            (Gt _ _) -> error "[Gt] Expects two integer values as arguments."
            (Eq _ _) -> error "[Eq] Expects two integer values as arguments."
            (If _ _ _) -> error "[If] Expects a boolean value as argument to decide a expression."
            (App _ _) -> error "[App] Expect a Function as first argument."

-------------------------- Semántica estática. ----------------------------------

-- Dos tipos posibles, entero y booleano. Que necesitamos que sean comparables.

data Type = Integer | Boolean
            deriving(Eq)

type Decl = (Identifier, Type)
type TypCtxt = [Decl]

{--
    vt:

    Verifica el tipo de una expresión de manera que para cada caso, aplicando pa-
    ra cada caso, la regla que le corresponda.
-}
vt :: TypCtxt -> Expr -> Type -> Bool
vt [] (V x) t = False
vt ((x,t):xs) (V x1) t1 = if x == x1 && t == t1
                          then True
                          else vt xs (V x1) t1
vt _ (I n) t = t == Integer
vt _ (B b) t = t == Boolean
vt c (Add e1 e2) Integer = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Mul e1 e2) Integer = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Succ e) Integer = (vt c e Integer)
vt c (Pred e) Integer = (vt c e Integer)
vt c (And e1 e2) Boolean = (vt c e1 Boolean) && (vt c e2 Boolean)
vt c (Or e1 e2) Boolean = (vt c e1 Boolean) && (vt c e2 Boolean)
vt c (Not e) Boolean = (vt c e Boolean)
vt c (Lt e1 e2) Boolean = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Gt e1 e2) Boolean = (vt c e1 Integer) && (vt c e2 Integer)
vt c (Eq e1 e2) Boolean = (vt c e1 Integer) && (vt c e2 Integer)
vt c (If b et ef) t = (vt c b Boolean) && (vt c et t) && (vt c ef t)
vt c (Let x e1 e2) t = if (vt c e1 Integer)
                       then vt ((x,Integer):c) e2 t
                       else vt ((x,Boolean):c) e2 t
vt _ _ _ = error "Error in types."
-- Cambiar por un union en el let. --
-- delete \\
-- $ ahorra parentesis.

{--
    eval:

    Primero verifica que el tipo de la expresión sea el correcto. Sí es correcto,
    entonces hace la evaluación. En caso de que no lo sea, devuelve un error re-
    lacionado con los tipos de las entradas.
-}
eval :: Expr -> Type -> Expr
eval e t = if vt [] e t
           then evale e
           else error "Error in the type of parameters."
