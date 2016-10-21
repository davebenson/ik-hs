

data Expr = CosParam Int
          | SinParam Int
          | Exact Int
          | Float Double
          | Sum [Expr]
          | Product [Expr]
          deriving (Show)

-- helper function for Sum and Product which have simple integer identities.
simplifySubexprForFlatMap :: Int -> Expr -> [Expr]
simplifySubexprForFlatMap identityInt testExpr =
  case simplifyExpr testExpr of
    Exact identityInt -> []
    rv -> [rv]


-- split constants
groupConstants :: [Expr] -> ([Expr], [Expr], [Expr])
groupConstants expr_list =
  let categorizeForFold (intexprs, floatexprs, otherexprs) expr =
           case expr of
             Exact _ -> (expr:intexprs, floatexprs, otherexprs)
             Float _ -> (intexprs, expr:floatexprs, otherexprs)
             _ ->       (intexprs, floatexprs, expr:otherexprs)
  in  foldl categorizeForFold ([], [], []) expr_list


--- product utilities ---
simplifySubexprForProduct :: Expr -> [Expr]
simplifySubexprForProduct (Product args) = args >>= simplifySubexprForProduct
simplifySubexprForProduct expr = simplifySubexprForFlatMap 1 expr
  
multipleExactExprs exprs = foldl multiply_exact_ints 1 any
                     where multiply_exact_ints ivalue (Exact ii) = ivalue * ii
multipleDoubleExprs exprs = foldl multiply_floats 1.0 any
                     where multiply_floats ivalue (Float ii) = ivalue * ii

productOfConstants :: [Expr] -> [Expr] -> [Expr]
productOfConstants [] [] = []
productOfConstants any [] = [Exact (multipleExactExprs any)]
productOfConstants iexprs fexprs = [Float ((multipleExactExprs iexprs) * (multipleDoubleExprs fexprs))]

--- sum utilities ---
simplifySubexprForSum :: Expr -> [Expr]
simplifySubexprForSum (Sum args) = flatMap simplifySubexprForSum args
simplifySubexprForSum expr = simplifySubexprForFlatMap 0 expr
  
sumExactExprs exprs = foldl multiply_exact_ints 1 any
                     where multiply_exact_ints ivalue (Exact ii) = ivalue * ii
sumDoubleExprs exprs = foldl multiply_floats 1.0 any
                     where multiply_floats ivalue (Float ii) = ivalue * ii

sumOfConstants :: [Expr] -> [Expr] -> [Expr]
sumOfConstants [] [] = []
sumOfConstants any [] = [Exact (multipleExactExprs any)]
sumOfConstants iexprs fexprs = [Float ((multipleExactExprs iexprs) * (multipleDoubleExprs fexprs))]

--- simplifications ---
simplifyExpr :: Expr -> Expr
simplifyExpr (Product elements) =
  -- handle nested products and identity elements
  case flatMap simplifySubexprForProduct elements of
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
            other ->
              if (find (\ a -> a == (Exact 0)) other) then (Exact 0)
              else Product other

simplifyExpr Sum elements =
  case flatMap simplifySubexprForSum elements of
    [] -> Exact 0
    [x] -> x
    simplified ->
      case (groupConstants simplified) of
        ([], [], _) -> Sum simplified
        ([_], [], _) -> Sum simplified
        ([], [_], _) -> Sum simplified
        (c1, c2, nonconst) ->
          case ((sumOfConstants c1 c2) ++ nonconst) of
            [] -> Exact 1
            [x] -> x
            other ->
              Sum other

simplifyExpr other = other


type AffineExpr = (Expr, Expr, Expr, Expr,
                   Expr, Expr, Expr, Expr,
                   Expr, Expr, Expr, Expr)
           
affineProduct :: AffineExpr -> AffineExpr -> AffineExpr
affineProduct (a11, a12, a13, a14, 
               a21, a22, a23, a24, 
               a31, a32, a33, a34) (b11, b12, b13, b14, 
                                    b21, b22, b23, b24, 
                                    b31, b32, b33, b34) =
  ((simplifyExpr Sum [(Product [a11 b11]) (Product [a12 b21]) (Product [a13 b31])])
   (simplifyExpr Sum [(Product [a11 b12]) (Product [a12 b22]) (Product [a13 b32])])
   (simplifyExpr Sum [(Product [a11 b13]) (Product [a12 b23]) (Product [a13 b33])])
   (simplifyExpr Sum [(Product [a11 b13]) (Product [a12 b23]) (Product [a13 b33] a14)])

   (simplifyExpr Sum [(Product [a21 b11]) (Product [a22 b21]) (Product [a23 b31])])
   (simplifyExpr Sum [(Product [a21 b12]) (Product [a22 b22]) (Product [a23 b32])])
   (simplifyExpr Sum [(Product [a21 b13]) (Product [a22 b23]) (Product [a23 b33])])
   (simplifyExpr Sum [(Product [a21 b13]) (Product [a22 b23]) (Product [a23 b33] a24)])

   (simplifyExpr Sum [(Product [a31 b11]) (Product [a32 b21]) (Product [a33 b31])])
   (simplifyExpr Sum [(Product [a31 b12]) (Product [a32 b22]) (Product [a33 b32])])
   (simplifyExpr Sum [(Product [a31 b13]) (Product [a32 b23]) (Product [a33 b33])])
   (simplifyExpr Sum [(Product [a31 b13]) (Product [a32 b23]) (Product [a33 b33] a34)]))


affineSum :: AffineExpr -> AffineExpr -> AffineExpr
affineSum (a11, a12, a13, a14, 
           a21, a22, a23, a24, 
           a31, a32, a33, a34) (b11, b12, b13, b14, 
                                b21, b22, b23, b24, 
                                b31, b32, b33, b34) =
  ((simplifyExpr Sum [a11, b11])
   (simplifyExpr Sum [a12, b12])
   (simplifyExpr Sum [a13, b13])
   (simplifyExpr Sum [a14, b14])

   (simplifyExpr Sum [a21, b21])
   (simplifyExpr Sum [a22, b22])
   (simplifyExpr Sum [a23, b23])
   (simplifyExpr Sum [a24, b24])

   (simplifyExpr Sum [a31, b31])
   (simplifyExpr Sum [a32, b32])
   (simplifyExpr Sum [a33, b33])
   (simplifyExpr Sum [a34, b34]))

-- Constructing the transform --


rotateX :: Expr -> Expr -> AffineExpr
rotateX sinExpr cosExpr =
  ((Exact 1) (Exact 0) (Exact 0) (Exact 0)
   (Exact 0)  cosExpr (Negate sinExpr) (Exact 0)
   (Exact 0)  sinExpr cosExpr (Exact 0))

rotateY :: Expr -> Expr -> AffineExpr
rotateY sinExpr cosExpr =
  (cosExpr (Exact 0) sinExpr (Exact 0)
   (Exact 0)  (Exact 1) (Exact 0) (Exact 0)
   (Negate sinExpr)  (Exact 0) cosExpr (Exact 0))

rotateZ :: Expr -> Expr -> AffineExpr
rotateZ sinExpr cosExpr =
  (cosExpr (Negate sinExpr) (Exact 0) (Exact 0)
   sinExpr cosExpr (Exact 0) (Exact 0)
   (Exact 0) (Exact 0) (Exact 1) (Exact 0))

translate :: Expr -> Expr -> Expr -> AffineExpr
translate tx ty tz =
  ((Exact 1) (Exact 0) (Exact 0) tx
   (Exact 0) (Exact 1) (Exact 0) ty
   (Exact 0) (Exact 0) (Exact 1) tz)
translateX expr = translate expr (Exact 0) (Exact 0)
translateY expr = translate (Exact 0) expr (Exact 0)
translateZ expr = translate (Exact 0) (Exact 0) expr

data ConstantAngle = PiFrac Int Int | Real Float


normalizePiFrac :: Int -> Int -> (Int,Int)
normalizePiFrac n d | d < 0 = normalizePiFrac -n d
                    | n < 0 = normalizePiFrac (n + 2 * d) d
                    | n > 2 * d = normalizePiFrac (n - 2 * d) d
                    | otherwise = (n, d)            -- TODO: compute GCD and normalize that way...

computeSinConstantAngle :: ConstantAngle -> Expr
computeSinConstantAngle (PiFrac n d) =
  case normalizePiFrac n d of
    (0,_) ->  (Exact 0)
    (1,1)  -> (Exact 0)
    (2,1)  -> (Exact 0)
    (1,2)  -> (Exact 1)
    (3,2)  -> (Exact -1)
    other  -> (Float (cos (n / d)))

computeCosConstantAngle :: ConstantAngle -> Expr
computeCosConstantAngle (PiFrac n d) =
  case normalizePiFrac n d of
    (0,_) ->  (Exact 1)
    (1,1)  -> (Exact -1)
    (2,1)  -> (Exact 1)
    (1,2)  -> (Exact 0)
    (3,2)  -> (Exact 0)
    other  -> (Float (sin (n / d)))

-- Constructing the transform --
--                             d       theta     r    alpha
data DHJointParams = Revolute Float ConstantAngle Float ConstantAngle 
convertDHJointParamsToAffine :: DHJointParams -> Int -> AffineExpr
convertDHJointParamsToAffine (Revolute d theta r alpha) = 
  let sinTheta = computeSinConstAngle theta
      cosTheta = computeCosConstAngle theta
      sinAlpha = computeSinConstAngle alpha
      cosAlpha = computeCosConstAngle alpha
  in   (translateZ d) `affineProduct`
       (rotZ sinTheta cosTheta) `affineProduct`
       (translateX d) `affineProduct`
       (rotX sinAlpha cosAlpha)

convertDHParamsToAffine :: [DHJointParams] -> AffineExpr
convertDHParamsToAffine jps =
   let affines = zipWith convertDHJointParamsToAffine jps [0...length(jps)-1]
   in  foldl affineProduct identityAffine affines


dhParams = [ Revolute 1.0 (PiFrac 0 1) 0.5 (PiFrac 0 1) ]
main = putStrLn (show convertDHJointParamsToAffine dhparams)
