
import Debug.Trace (trace)
import Data.List (intersperse, sortBy)

data Expr = CosParam Int
          | SinParam Int
          | Exact Int
          | ConstFloat Double
          | Sum [Expr]
          | Product [Expr]
          deriving (Show)

addParens str = "(" ++ str ++ ")"
exprToString' (CosParam i) containingPrec =
   "cos o" ++ (show i)
exprToString' (SinParam i) containingPrec =
   "sin o" ++ (show i)
exprToString' (Exact i) containingPrec =
   (show i)
exprToString' (ConstFloat i) containingPrec =
   (show i)
exprToString' (Sum exprs) prec =
   if prec < 1 then
     concat (intersperse " + " (map (\ e -> exprToString' e 1) exprs))
   else
     addParens (exprToString' (Sum exprs) 0)
exprToString' (Product exprs) prec =
   if prec < 2 then
     concat (intersperse " * " (map (\ e -> exprToString' e 2) exprs))
   else
     addParens (exprToString' (Product exprs) 0)
--exprToString' (Negate expr) _ =
--   "-" ++ (exprToString' expr 2)
exprToString expr = exprToString' expr 0



-- helper function for Sum and Product which have simple integer identities.
simplifySubexprForFlatMap :: Int -> Expr -> [Expr]
simplifySubexprForFlatMap identityInt testExpr =
  case simplifyExpr testExpr of
    Exact ii | ii == identityInt -> []
             | otherwise -> [Exact ii]
    rv -> [rv]


-- split constants
groupConstants :: [Expr] -> ([Expr], [Expr], [Expr])
groupConstants expr_list =
  let categorizeForFold (intexprs, floatexprs, otherexprs) expr =
           case expr of
             Exact _ -> (expr:intexprs, floatexprs, otherexprs)
             ConstFloat _ -> (intexprs, expr:floatexprs, otherexprs)
             _ ->       (intexprs, floatexprs, expr:otherexprs)
  in  foldl categorizeForFold ([], [], []) expr_list


--- product utilities ---
simplifySubexprForProduct :: Expr -> [Expr]
simplifySubexprForProduct (Product args) = args >>= simplifySubexprForProduct
simplifySubexprForProduct expr = simplifySubexprForFlatMap 1 expr
  
multiplyExactExprs :: [Expr] -> Int
multiplyExactExprs exprs = let multiply_exact_ints ivalue (Exact ii) = ivalue * ii
                           in  foldl multiply_exact_ints 1 exprs

multiplyDoubleExprs :: [Expr] -> Double
multiplyDoubleExprs exprs = let multiply_floats fvalue (ConstFloat ff) = fvalue * ff
                            in  foldl multiply_floats 1.0 exprs

productOfConstants :: [Expr] -> [Expr] -> [Expr]
productOfConstants [] [] = []
productOfConstants exprs [] = [Exact (multiplyExactExprs exprs)]
productOfConstants iexprs fexprs = [ConstFloat ((fromIntegral (multiplyExactExprs iexprs)) * (multiplyDoubleExprs fexprs))]

--- sum utilities ---
simplifySubexprForSum :: Expr -> [Expr]
simplifySubexprForSum (Sum args) = args >>= simplifySubexprForSum
simplifySubexprForSum expr = simplifySubexprForFlatMap 0 expr
  
sumExactExprs exprs = let multiply_exact_ints ivalue (Exact ii) = ivalue * ii
                      in  foldl multiply_exact_ints 1 exprs
sumDoubleExprs exprs = foldl multiply_floats 1.0 exprs
                     where multiply_floats ivalue (ConstFloat ii) = ivalue * ii

sumOfConstants :: [Expr] -> [Expr] -> [Expr]
sumOfConstants [] [] = []
sumOfConstants exprs [] = [Exact (sumExactExprs exprs)]
sumOfConstants iexprs fexprs = [ConstFloat (fromIntegral (sumExactExprs iexprs) * (sumDoubleExprs fexprs))]

--- simplifications ---
isExactInt :: Int -> Expr -> Bool
isExactInt i e =
  case e of
    Exact ii -> i == ii
    _        -> False

simplifyExprProduct_1_and_constants (Product elements) =
  -- handle nested products and identity elements
  case (map simplifyExpr elements) >>= simplifySubexprForProduct of
    [] -> Exact 1
    [x] -> x
    simplified ->
      case (groupConstants simplified) of
        ([], [], _) -> Product simplified
        ([_], [], _) -> Product simplified
        ([], [_], _) -> Product simplified
        (c1, c2, nonconst) ->
          case ((productOfConstants c1 c2) ++ nonconst) of
            [] -> Exact 1
            [x] -> x
            other -> (Product other)

simplifyProductOf0 (Product elements) =
  if any (isExactInt 0) elements then Exact 0
  else                                Product elements
simplifyProductOf0 other = other

--simplifyExprProduct_Negates (Product elements) =
--  let   doFoldl (denegated, negcount) (Negate expr) = (expr:denegated, negcount+1)
--        doFoldl (denegated, negcount) (Exact (-1)) = (denegated, negcount+1)
--        doFoldl (denegated, negcount) expr = (expr:denegated, negcount)
--        (denegated, negcount) = foldl doFoldl ([], 0) elements
--  in if negcount `mod` 2 == 0 then (Product denegated)
--     else                      Negate (Product denegated)

simplifyExprProduct_Negates other = other

simplifyExprProduct = simplifyProductOf0 . simplifyExprProduct_1_and_constants

simplifyExpr :: Expr -> Expr

simplifyExpr (Product elements) = simplifyExprProduct (Product (map simplifyExpr elements))

simplifyExpr (Sum elements) =
  case (map simplifyExpr elements) >>= simplifySubexprForSum of
    [] -> Exact 0
    [x] -> x
    simplified ->
      case (groupConstants simplified) of
        ([], [], _) -> Sum simplified
        ([_], [], _) -> Sum simplified
        ([], [_], _) -> Sum simplified
        (c1, c2, nonconst) ->
          case ((sumOfConstants c1 c2) ++ nonconst) of
            [] -> Exact 0
            [x] -> x
            other ->
              Sum other

--simplifyExpr (Negate expr) =
--  case simplifyExpr expr of
--    (Negate x) -> x
--    (Exact x) -> Exact (-x)
--    (ConstFloat x) -> ConstFloat (-x)
--    x -> Negate x


simplifyExpr other = other


type AffineExpr = (Expr, Expr, Expr, Expr,
                   Expr, Expr, Expr, Expr,
                   Expr, Expr, Expr, Expr)
affineToString (a11, a12, a13, a14, 
                a21, a22, a23, a24, 
                a31, a32, a33, a34) =
  "[ " ++ (exprToString a11) ++ "\n" ++
  "  " ++ (exprToString a12) ++ "\n" ++
  "  " ++ (exprToString a13) ++ "\n" ++
  "  " ++ (exprToString a14) ++ ";\n" ++
  "  " ++ (exprToString a21) ++ "\n" ++
  "  " ++ (exprToString a22) ++ "\n" ++
  "  " ++ (exprToString a23) ++ "\n" ++
  "  " ++ (exprToString a24) ++ ";\n" ++
  "  " ++ (exprToString a31) ++ "\n" ++
  "  " ++ (exprToString a32) ++ "\n" ++
  "  " ++ (exprToString a33) ++ "\n" ++
  "  " ++ (exprToString a34) ++ " ]\n"
           
affineProduct  :: AffineExpr -> AffineExpr -> AffineExpr
affineProduct  (a11, a12, a13, a14, 
                a21, a22, a23, a24, 
                a31, a32, a33, a34) (b11, b12, b13, b14, 
                                     b21, b22, b23, b24, 
                                     b31, b32, b33, b34) =
  let  c11 = simplifyExpr (Sum [(Product [a11, b11]), (Product [a12, b21]), (Product [a13, b31])])
       c12 = simplifyExpr (Sum [(Product [a11, b12]), (Product [a12, b22]), (Product [a13, b32])])
       c13 = simplifyExpr (Sum [(Product [a11, b13]), (Product [a12, b23]), (Product [a13, b33])])
       c14 = simplifyExpr (Sum [(Product [a11, b14]), (Product [a12, b24]), (Product [a13, b34]), a14])

       c21 = simplifyExpr (Sum [(Product [a21, b11]), (Product [a22, b21]), (Product [a23, b31])])
       c22 = simplifyExpr (Sum [(Product [a21, b12]), (Product [a22, b22]), (Product [a23, b32])])
       c23 = simplifyExpr (Sum [(Product [a21, b13]), (Product [a22, b23]), (Product [a23, b33])])
       c24 = simplifyExpr (Sum [(Product [a21, b14]), (Product [a22, b24]), (Product [a23, b34]), a24])

       c31 = simplifyExpr (Sum [(Product [a31, b11]), (Product [a32, b21]), (Product [a33, b31])])
       c32 = simplifyExpr (Sum [(Product [a31, b12]), (Product [a32, b22]), (Product [a33, b32])])
       c33 = simplifyExpr (Sum [(Product [a31, b13]), (Product [a32, b23]), (Product [a33, b33])])
       c34 = simplifyExpr (Sum [(Product [a31, b14]), (Product [a32, b24]), (Product [a33, b34]), a34])
  in (c11, c12, c13, c14, 
      c21, c22, c23, c24, 
      c31, c32, c33, c34)

applyToAffine f (a11, a12, a13, a14, 
                 a21, a22, a23, a24, 
                 a31, a32, a33, a34) = (f a11, f a12, f a13, f a14, 
                                        f a21, f a22, f a23, f a24, 
                                        f a31, f a32, f a33, f a34)

simplifyAffine aff = applyToAffine (sortProducts . distributeExpr . simplifyExpr) aff

affineSum :: AffineExpr -> AffineExpr -> AffineExpr
affineSum (a11, a12, a13, a14, 
           a21, a22, a23, a24, 
           a31, a32, a33, a34) (b11, b12, b13, b14, 
                                b21, b22, b23, b24, 
                                b31, b32, b33, b34) =
  (simplifyExpr (Sum [a11, b11]),
   simplifyExpr (Sum [a12, b12]),
   simplifyExpr (Sum [a13, b13]),
   simplifyExpr (Sum [a14, b14]),
                 
   simplifyExpr (Sum [a21, b21]),
   simplifyExpr (Sum [a22, b22]),
   simplifyExpr (Sum [a23, b23]),
   simplifyExpr (Sum [a24, b24]),
                 
   simplifyExpr (Sum [a31, b31]),
   simplifyExpr (Sum [a32, b32]),
   simplifyExpr (Sum [a33, b33]),
   simplifyExpr (Sum [a34, b34]))

affineIdentity :: AffineExpr
affineIdentity = 
  ((Exact 1), (Exact 0), (Exact 0), (Exact 0),
   (Exact 0), (Exact 1), (Exact 0), (Exact 0),
   (Exact 0), (Exact 0), (Exact 1), (Exact 0))

-- Constructing the transform --


negateExpr expr = simplifyExpr (Product [(Exact (-1)), expr])

rotateX :: Expr -> Expr -> AffineExpr
rotateX sinExpr cosExpr =
  ((Exact 1), (Exact 0), (Exact 0), (Exact 0),
   (Exact 0),  cosExpr, negateExpr sinExpr, (Exact 0),
   (Exact 0),  sinExpr, cosExpr, (Exact 0))

rotateY :: Expr -> Expr -> AffineExpr
rotateY sinExpr cosExpr =
  (cosExpr, (Exact 0), sinExpr, (Exact 0),
   (Exact 0),  (Exact 1), (Exact 0), (Exact 0),
   negateExpr sinExpr,  (Exact 0), cosExpr, (Exact 0))

rotateZ :: Expr -> Expr -> AffineExpr
rotateZ sinExpr cosExpr =
  (cosExpr, negateExpr sinExpr, (Exact 0), (Exact 0),
   sinExpr, cosExpr, (Exact 0), (Exact 0),
   (Exact 0), (Exact 0), (Exact 1), (Exact 0))

translate :: Expr -> Expr -> Expr -> AffineExpr
translate tx ty tz =
  ((Exact 1), (Exact 0), (Exact 0), tx,
   (Exact 0), (Exact 1), (Exact 0), ty,
   (Exact 0), (Exact 0), (Exact 1), tz)
translateX :: Expr -> AffineExpr
translateX expr = translate expr (Exact 0) (Exact 0)
translateY :: Expr -> AffineExpr
translateY expr = translate (Exact 0) expr (Exact 0)
translateZ :: Expr -> AffineExpr
translateZ expr = translate (Exact 0) (Exact 0) expr

data ConstantAngle = PiFrac Int Int | Real Double


normalizePiFrac :: Int -> Int -> (Int,Int)
normalizePiFrac n d | d < 0 = normalizePiFrac (-n) d
                    | n < 0 = normalizePiFrac (n + 2 * d) d
                    | n > 2 * d = normalizePiFrac (n - 2 * d) d
                    | otherwise = (n, d)            -- TODO: compute GCD and normalize that way...

computeSinConstantAngle :: ConstantAngle -> Expr
computeSinConstantAngle (PiFrac n d) =
  case normalizePiFrac n d of
    (0,_)  ->  (Exact 0)
    (1,1)  -> (Exact 0)
    (2,1)  -> (Exact 0)
    (1,2)  -> (Exact 1)
    (3,2)  -> (Exact (-1))
    _      -> (ConstFloat (cos ((fromIntegral n) / (fromIntegral d))))

computeCosConstantAngle :: ConstantAngle -> Expr
computeCosConstantAngle (PiFrac n d) =
  case normalizePiFrac n d of
    (0,_)  ->  (Exact 1)
    (1,1)  -> (Exact (-1))
    (2,1)  -> (Exact 1)
    (1,2)  -> (Exact 0)
    (3,2)  -> (Exact 0)
    _      -> (ConstFloat (sin ((fromIntegral n) / (fromIntegral d))))

makeConstExpr f | f == 0.0 = Exact 0
                | otherwise = ConstFloat f

arbitraryCartesianProduct :: [[Expr]] -> [[Expr]]
arbitraryCartesianProduct [] = [[]]
arbitraryCartesianProduct (head:tail) =
  let addHeadsToAllLists listoflists hvalue = (map (\ list -> hvalue : list) listoflists)
  in  head >>= (addHeadsToAllLists (arbitraryCartesianProduct tail))


compareTerms :: Expr -> Expr -> Ordering
compareTerms (Exact _) (Exact _) = EQ
compareTerms (Exact _) _ = LT
compareTerms _ (Exact _) = GT
compareTerms (ConstFloat _) (ConstFloat _) = EQ
compareTerms (ConstFloat _) _ = LT
compareTerms _ (ConstFloat _) = GT
compareTerms (CosParam x) (CosParam y) =
  if x < y then 
    LT
  else if x > y then 
    GT
  else
    EQ
compareTerms (CosParam x) _ = LT
compareTerms _ (CosParam x) = GT
compareTerms (SinParam x) (SinParam y) =
  if x < y then 
    LT
  else if x > y then 
    GT
  else
    EQ
compareTerms (SinParam x) _ = LT
compareTerms _ (SinParam x) = GT
compareTerms _ _ = EQ
  


distributeExpr (Product elements) =
  let toSumList (listofsumlists) (Sum list) = list : listofsumlists
      toSumList (listofsumlists) (Product list) = (foldl toSumList [] (map distributeExpr list)) ++ listofsumlists
      toSumList (listofsumlists) other = [other] : listofsumlists
      sopForm = arbitraryCartesianProduct (foldl toSumList [] (map distributeExpr elements))
      listOfProducts = map Product sopForm
  in
      simplifyExpr (Sum listOfProducts)
distributeExpr (Sum elements) =
  simplifyExpr (Sum (map distributeExpr elements))
distributeExpr other = other

sortProducts (Product elements) = Product (sortBy compareTerms elements)
sortProducts (Sum x) = Sum (map sortProducts x)
sortProducts x = x

-- Constructing the transform --
--                             d        theta        r       alpha
--     (r is sometime known as a)
data DHJointParams = Revolute Double ConstantAngle Double ConstantAngle 
convertDHJointParamsToAffineList :: DHJointParams -> Int -> [AffineExpr]
convertDHJointParamsToAffineList (Revolute d theta r alpha) whichJoint = 
  let sinTheta = computeSinConstantAngle theta
      cosTheta = computeCosConstantAngle theta
      sinAlpha = computeSinConstantAngle alpha
      cosAlpha = computeCosConstantAngle alpha
  in   [(translateZ (makeConstExpr d)),
        (rotateZ sinTheta cosTheta),
        (rotateZ (SinParam whichJoint) (CosParam whichJoint)),
        (translateX (makeConstExpr r)),
        (rotateX sinAlpha cosAlpha)]


--convertDHJointParamsToAffine :: DHJointParams -> Int -> AffineExpr
--convertDHJointParamsToAffine jp ind =
--    foldl (\ j -> (convertDHJointParamsToAffineList j ind)) identityAffine jp

convertDHParamsToAffineList :: [DHJointParams] -> [AffineExpr]
convertDHParamsToAffineList jointParams =
  concat (zipWith convertDHJointParamsToAffineList jointParams [0..])

computeAffineListProduct :: [AffineExpr] -> AffineExpr
computeAffineListProduct exprs =
  foldl affineProduct affineIdentity exprs

convertDHParamsToAffine :: [DHJointParams] -> AffineExpr
convertDHParamsToAffine = computeAffineListProduct . convertDHParamsToAffineList

dhparams = [ Revolute 0.089159 (PiFrac 0 1) 0.0 (PiFrac 1 2),
             Revolute 0.0 (PiFrac (-1) 2) (-0.425) (PiFrac 0 1),
             Revolute 0.0 (PiFrac 0 1) (-0.39225) (PiFrac 0 1),
             Revolute 0.10915 (PiFrac 0 1) 0.0 (PiFrac 1 2),
             Revolute 0.09465 (PiFrac 0 1) 0.0 (PiFrac (-1) 2),
             Revolute 0.0823 (PiFrac 0 1) 0.0 (PiFrac 0 1) ]


--main = putStrLn (concat (map affineToString (convertDHJointParamsToAffineList (head dhparams) 3)))
--main = putStrLn (affineToString (computeAffineListProduct (convertDHJointParamsToAffineList (head dhparams) 3)))
main = putStrLn (affineToString (simplifyAffine (convertDHParamsToAffine dhparams)))
--main = putStrLn (concat (map affineToString (convertDHParamsToAffineList dhparams)))

--main = putStrLn (show ((convertDHParamsToAffineList dhparams)))
--main = putStrLn (affineToString ((rotateX (SinParam 0) (CosParam 0)) `affineProduct` (rotateX (SinParam 0) (CosParam 0))))
--main = putStrLn (exprToString (simplifyExpr (Product [(Negate (CosParam 0)), (Product [Negate (CosParam 0), (Exact 2)])])))

--bigexpr = Sum [Product [Sum [negateExpr (Product [Sum [negateExpr (Product [SinParam 3,Sum [negateExpr (Product [CosParam 1,SinParam 2]),negateExpr (Product [SinParam 1,CosParam 2])]]),negateExpr (Product [CosParam 3,Sum [Product [CosParam 2,CosParam 1],negateExpr (Product [SinParam 2,SinParam 1])]])],CosParam 4]),Product [Sum [Product [Sum [negateExpr (Product [CosParam 1,SinParam 2]),negateExpr (Product [SinParam 1,CosParam 2])],CosParam 3],negateExpr (Product [Sum [Product [CosParam 2,CosParam 1],negateExpr (Product [SinParam 2,SinParam 1])],SinParam 3])],SinParam 4]],CosParam 5],Product [Sum [Product [Sum [negateExpr (Product [SinParam 3,Sum [negateExpr (Product [CosParam 1,SinParam 2]),negateExpr (Product [SinParam 1,CosParam 2])]]),negateExpr (Product [CosParam 3,Sum [Product [CosParam 2,CosParam 1],negateExpr (Product [SinParam 2,SinParam 1])]])],SinParam 4],Product [Sum [Product [Sum [negateExpr (Product [CosParam 1,SinParam 2]),negateExpr (Product [SinParam 1,CosParam 2])],CosParam 3],negateExpr (Product [Sum [Product [CosParam 2,CosParam 1],negateExpr (Product [SinParam 2,SinParam 1])],SinParam 3])],CosParam 4]],SinParam 5]]
--tinyexpr = Product [negateExpr (Sum [CosParam 0, CosParam 1]), Sum [SinParam 0, SinParam 1]]
--main = putStrLn (exprToString (sortProducts (distributeExpr bigexpr)))


