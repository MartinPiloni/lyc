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

{- Ω ≈ (Σ' + Z × Ω + Z → Ω)⊥ -}
data Ω = Normal Σ | Abort Σ | Out (Int, Ω) | In (Int -> Ω)
{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
   * Out    : (Z, Ω) → Ω
   * In     : (Z → Ω) → Ω
-}

data Expr a where
  -- Expresiones enteras
  Const  :: Int       -> Expr Int                      -- n
  Var    :: String    -> Expr Int                      -- v
  Plus   :: Expr Int  -> Expr Int -> Expr Int          -- e + e'
  Dif    :: Expr Int  -> Expr Int -> Expr Int          -- e - e'
  Times  :: Expr Int  -> Expr Int -> Expr Int          -- e * e'
  Div    :: Expr Int  -> Expr Int -> Expr Int          -- e / e' (div entera)

  -- Expresiones booleanas
  Eq     :: Expr Int  -> Expr Int -> Expr Bool         -- e = e'
  Neq    :: Expr Int  -> Expr Int -> Expr Bool         -- e /= e'
  Less   :: Expr Int  -> Expr Int -> Expr Bool         -- e < e'
  Leq    :: Expr Int  -> Expr Int -> Expr Bool         -- e <= e'
  And    :: Expr Bool -> Expr Bool -> Expr Bool        -- e && e'
  Or     :: Expr Bool -> Expr Bool -> Expr Bool        -- b || b'
  Not    :: Expr Bool -> Expr Bool                     -- ¬b

  -- Comandos
  Skip   :: Expr Ω                                     -- skip
  Local  :: Iden -> Expr Int -> Expr Ω -> Expr Ω       -- newvar v := e in c
  Assign :: Iden -> Expr Int -> Expr Ω                 -- v := e
  Fail   :: Expr Ω                                     -- fail
  Catch  :: Expr Ω -> Expr Ω -> Expr Ω                 -- catch c with c'
  While  :: Expr Bool -> Expr Ω -> Expr Ω              -- while b do c
  If     :: Expr Bool -> Expr Ω -> Expr Ω -> Expr Ω    -- if b then c else c'
  Seq    :: Expr Ω -> Expr Ω -> Expr Ω                 -- c ; c'
  Output :: Expr Int -> Expr Ω                         -- !e
  Input  :: Iden -> Expr Ω                             -- ?x
    
class DomSem dom where 
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (Const a)     _ = a
  sem (Var v)       σ = σ v
  sem (Plus e1 e2)  σ = sem e1 σ + sem e2 σ
  sem (Dif e1 e2)   σ = sem e1 σ - sem e2 σ
  sem (Times e1 e2) σ = sem e1 σ * sem e2 σ
  sem (Div e1 e2)   σ =
    if sem e2 σ == 0 
        then 0
        else sem e1 σ `div` sem e2 σ

instance DomSem Bool where
  sem (Eq e1 e2)   σ = sem e1 σ == sem e2 σ
  sem (Neq e1 e2)  σ = sem e1 σ /= sem e2 σ
  sem (Less e1 e2) σ = sem e1 σ < sem e2 σ
  sem (Leq e1 e2)  σ = sem e1 σ <= sem e2 σ
  sem (And e1 e2)  σ = sem e1 σ && sem e2 σ
  sem (Or e1 e2)   σ = sem e1 σ || sem e2 σ
  sem (Not e1)     σ = not (sem e1 σ)
 
(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ)  = f σ
(*.) _ (Abort σ)   = Abort σ
(*.) f (Out (n,ω)) = Out (n, f *. ω)
(*.) f (In g)      = In ((f *.) . g)

(†.) :: (Σ -> Σ) -> Ω -> Ω
(†.) f (Normal σ)  = Normal $ f σ
(†.) f (Abort σ)   = Abort $ f σ
(†.) f (Out (n,ω)) = Out (n, f †. ω)
(†.) f (In g)      = In ((f †.) . g)

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ)  = Normal σ
(+.) f (Abort σ)   = f σ
(+.) f (Out (n,ω)) = Out (n, f +. ω)
(+.) f (In g)      = In ((f +.) . g)

instance DomSem Ω where
  sem Skip          σ = Normal σ
  sem (Local v e c) σ = (†.) (\s -> update s v (σ v)) (sem c (update σ v (sem e σ)))
  sem (Assign v e)  σ = Normal (update σ v (sem e σ))
  sem Fail          σ = Abort σ
  sem (Catch c c')  σ = (+.) (\s -> sem c' s) (sem c σ)
  sem (While b c)   σ = fix (\w s -> if sem b s
                                     then (*.) w (sem c s)
                                     else Normal s) σ
  sem (If b c c')   σ =
    if sem b σ
      then sem c  σ
      else sem c' σ
  sem (Seq c c')    σ = (*.) (\s -> sem c' s) (sem c σ)
  sem (Output e)    σ = Out (sem e σ, Normal σ)
  sem (Input v)     σ = In (\x -> Normal (update σ v x))

{- ################# Funciones de evaluación de dom ################# -}

class Eval dom where 
  eval :: Expr dom -> Σ -> IO ()

instance Eval Int where
  eval e = print . sem e

instance Eval Bool where
  eval e = print . sem e

instance Eval Ω where
  eval e = unrollOmega . sem e
    where unrollOmega :: Ω -> IO ()
          unrollOmega (Normal σ)   = return ()
          unrollOmega (Abort σ)    = putStrLn "Abort"
          unrollOmega (Out (n, ω)) = print n >> unrollOmega ω
          unrollOmega (In f)       = getLine >>= unrollOmega . f . read

{- Dado un número por consola >= 0 calcula el factorial de ese número -}
progFact =
  Seq
    (Input "x")
    (Seq
      (If
        (Less (Var "x") (Const 0))
        Fail
        (Seq
          (Assign "y" (Const 1))
          (While
            (Leq (Const 1) (Var "x"))
            (Seq
              (Assign "y" (Times (Var "x") (Var "y")))
              (Assign "x" (Dif (Var "x") (Const 1)))
            )
          )
        )
      )
      (Output (Var "y"))
    )

factorial = eval progFact eIniTest

{- Dado un número por consola >= 0 calcula la suma de los numeros enteros de 1 al número ingresado -}
progSum =
    Seq
        (Input "n")
        (Seq
            (If
                (Less (Var "n") (Const 0))
                Fail
                (Seq
                    (Assign "r" (Const 0))
                    (While
                        (Less (Const 0) (Var "n"))
                        (Seq
                            (Assign "r" (Plus (Var "r") (Var "n")))
                            (Assign "n" (Dif (Var "n") (Const 1)))
                        )
                    )
                )
            )
            (Output (Var "r"))
        )

sumGauss = eval progSum eIniTest
