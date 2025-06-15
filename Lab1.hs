{-# LANGUAGE GADTs #-}

--         ∞
-- fix f = ⊔ fⁱ ⊥
--        i=0
fix :: (a -> a) -> a
fix f = f (fix f) 

type Iden = String
type Σ = Iden -> Int

-- Función de actualización de estado
update :: Σ -> Iden -> Int -> Σ
update σ v n v' =
  if v == v'
    then n
    else σ v'

eInicial, eIniTest :: Σ
eInicial = \v -> undefined
eIniTest = \v -> 0

{- Ω ≈ Σ + Σ -}
data Ω
  = Normal Σ
  | Abort Σ

{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
-}

data Expr a where
  -- Expresiones enteras
  -- n
  Const :: Int                  -> Expr Int
  -- v
  Var   :: Iden                 -> Expr Int
  -- e + e'
  Plus  :: Expr Int -> Expr Int -> Expr Int
  -- e - e'
  Dif   :: Expr Int -> Expr Int -> Expr Int
  -- e * e'
  Times :: Expr Int -> Expr Int -> Expr Int
  -- e / e' (división entera)
  Div   :: Expr Int -> Expr Int -> Expr Int
  -- Si e' evalúa a 0, hagan lo que quieran.

  {- Expresiones booleanas -}

  -- e = e'
  Eq   :: Expr Int  -> Expr Int -> Expr Bool
  -- e /= e'
  Neq  :: Expr Int  -> Expr Int -> Expr Bool
  -- e < e'
  Less :: Expr Int  -> Expr Int -> Expr Bool
  -- b && b'
  And  :: Expr Bool -> Expr Bool -> Expr Bool
  -- b || b'
  Or   :: Expr Bool -> Expr Bool -> Expr Bool
  -- ¬b
  Not  :: Expr Bool              -> Expr Bool

  {- Comandos -}

  -- SKIP
  Skip   ::                                    Expr Ω
  -- NEWVAR v := e IN c
  Local  :: Iden      -> Expr Int -> Expr Ω -> Expr Ω
  -- v := e
  Assign :: Iden      -> Expr Int           -> Expr Ω
  -- FAIL
  Fail   ::                                    Expr Ω
  -- CATCHIN c WITH c'
  Catch  :: Expr Ω    -> Expr Ω             -> Expr Ω
  -- WHILE b DO c
  While  :: Expr Bool -> Expr Ω             -> Expr Ω
  -- IF b THEN c ELSE c'
  If     :: Expr Bool -> Expr Ω   -> Expr Ω -> Expr Ω
  -- c ; c'
  Seq    :: Expr Ω    -> Expr Ω             -> Expr Ω

class DomSem dom where
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (Const a) _    = a
  sem (Var v) σ      = σ v
  sem (Plus e1 e2) σ = sem e1 σ + sem e2 σ
  sem (Dif e1 e2) σ = sem e1 σ - sem e2 σ
  sem (Times e1 e2) σ = sem e1 σ * sem e2 σ
  sem (Div e1 e2) σ =
    if sem e2 σ == 0 
        then 0
        else sem e1 σ `div` sem e2 σ

instance DomSem Bool where
  sem (Eq e1 e2) σ = sem e1 σ == sem e2 σ
  sem (Neq e1 e2) σ = sem e1 σ /= sem e2 σ
  sem (Less e1 e2) σ = sem e1 σ < sem e2 σ
  sem (And e1 e2) σ = sem e1 σ && sem e2 σ
  sem (Or e1 e2) σ = sem e1 σ || sem e2 σ
  sem (Not e1) σ = not (sem e1 σ)
  
(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ) = f σ
(*.) _ (Abort σ)  = Abort σ

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ) = Normal σ
(+.) f (Abort σ)  = f σ

(†.) :: (Σ -> Σ) -> Ω -> Ω
(†.) f (Normal σ) = Normal (f σ)
(†.) f (Abort σ)  = Abort (f σ)

instance DomSem Ω where
  sem Skip σ = Normal σ
  sem (Local v e c) σ = (†.) (\s -> update s v (σ v)) (sem c (update σ v (sem e σ)))
  sem (Assign v e) σ = Normal (update σ v (sem e σ))
  sem Fail σ = Abort σ
  sem (Catch c c') σ = (+.) (\s -> sem c' s) (sem c σ)
  sem (While b c) σ = fix (\w s -> if sem b s
                                     then (*.) w (sem c s)
                                     else Normal s) σ
  sem (If b c c') σ =
    if sem b σ
      then sem c σ
      else sem c' σ
  sem (Seq c c') σ = (*.) (\s -> sem c' s) (sem c σ)

{- ################# Funciones de evaluación de dom ################# -}
class Eval dom where
  eval :: [Iden] -> Expr dom -> Σ -> IO ()

instance Eval Int where
  eval _ e = print . sem e

instance Eval Bool where
  eval _ e = print . sem e

instance Eval Ω where
  eval lvars e = \sigma -> mapM_ (f (elsigma (sem e sigma))) lvars
    where
      elsigma (Normal σ) = σ
      elsigma (Abort σ)  = σ
      f s var = putStrLn (var ++ " vale " ++ (show (s var)))

{- Usen esto con eInicial o eIniTest pasando una lista de variables -}
prog1 = Assign "x" (Const 8)

ejemplo1 = eval ["x"] prog1 eIniTest

{- Debe devolver 4 en "x" y 5 en "y" -}

prog2 = Seq
          (Seq
            (Assign "x" (Const 3))
            (Assign "y" (Const 5))
          )
          (Assign "x"
            (Div (Plus (Var "x") (Var "y")) (Const 2))
          )

ejemplo2 = eval ["x", "y"] prog2 eInicial

{- Este programa debe comportarse como Skip -}

prog3 =
  Catch
    (Local "x" (Const 7) Fail)
    Skip

ejemplo3 = eval ["x"] prog3 eIniTest

{- División y Resto -}

progDivMod =
  If
    (Or
      (Or (Less (Var "y") (Const 0)) (Eq (Var "y") (Const 0)))
      (Less (Var "x") (Const 0))
    )
    Fail
    (Local "q" (Const 0)
      (Local "r" (Var "x")
        (Seq
          (Seq
            (While
              (Not (Less (Var "r") (Var "y")))
              (Seq
                (Assign "q" (Plus (Var "q") (Const 1)))
                (Assign "r" (Dif (Var "r") (Var "y")))
              )
            )
            (Assign "x" (Var "q"))
          )
          (Assign "y" (Var "r"))
        )
      )
    )

{- Ejecuta el programa de división entera a/b con a en "x" y b en "y". Devuelve
	el cociente en "x" y el resto en "y".
    Si "x" < 0 o "y" <= 0, aborta dejando los valores iniciales de "x" e "y".
-}

ejemploDivMod a b = eval ["x", "y"] progDivMod $
  update (update eInicial "x" a) "y" b

progWhile = Seq
              (Assign "x" (Const 3))
              (While (Not (Less (Var "x") (Const 0)))
                (Assign "x" (Dif (Var "x") (Const 1)))
              )

ejemploWhile = eval ["x"] progWhile eInicial


