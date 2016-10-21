

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
    Exact Int identityInt -> []
    rv -> [rv]

-- split constants
groupConstants :: [Expr] -> ([Expr], [Expr], [Expr])
groupConstants expr_list =
  foldl categorizeForFold ([], [], []) expr_list
     where categorizeForFold (intexprs floatexprs otherexprs) expr =
       case expr of
         Exact _ -> (expr:intexprs floatexprs otherexprs)
         Float _ -> (intexprs expr:floatexprs otherexprs)
         _ -> (intexprs floatexprs expr:otherexprs)

simplifyExpr :: Expr -> Expr
simplifyExpr Product elements =
  case flatmap (simplifySubexprForFlatMap 1) elements of
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
              if (...contains 0) then (Exact 0)
              else Product other

productOfConstants :: [Expr] -> [Expr] -> []
productOfConstants [] [] = []

simplifyExpr Sum elements =
  case flatmap (simplifySubexprForFlatMap 0) elements of
    [] -> Exact 1
    [x] -> x
    other -> if (find  (\ a -> if a == (Exact 0) ...exact 0...  other) -> 0
             else 
               ... split constants
simplifyExpr other = other


data Affine = (Expr Expr Expr Expr
               Expr Expr Expr Expr
               Expr Expr Expr Expr)
           
affineProduct :: Affine -> Affine -> Affine
affineProduct (a11 a12 a13 a14 
               a21 a22 a23 a24 
               a31 a32 a33 a34) (b11 b12 b13 b14 
                                 b21 b22 b23 b24 
                                 b31 b32 b33 b34) =
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


affineSum :: Affine -> Affine -> Affine
affineSum (a11 a12 a13 a14 
           a21 a22 a23 a24 
           a31 a32 a33 a34) (b11 b12 b13 b14 
                             b21 b22 b23 b24 
                             b31 b32 b33 b34) =
  ((simplifyExpr Sum [a11 b11])
   (simplifyExpr Sum [a12 b12])
   (simplifyExpr Sum [a13 b13])
   (simplifyExpr Sum [a14 b14])

   (simplifyExpr Sum [a21 b21])
   (simplifyExpr Sum [a22 b22])
   (simplifyExpr Sum [a23 b23])
   (simplifyExpr Sum [a24 b24])

   (simplifyExpr Sum [a31 b31])
   (simplifyExpr Sum [a32 b32])
   (simplifyExpr Sum [a33 b33])
   (simplifyExpr Sum [a34 b34]))

-- Constructing the transform --

data ConstantAngle = RealAngle Double
                   | PiFrac Int Int

rotXConstant :: ConstantAngle -> AffineExpr
  ...
rotYConstant :: ConstantAngle -> AffineExpr
  ...
rotZConstant :: ConstantAngle -> AffineExpr
  ...

translate :: Expr -> Expr -> Expr -> AffineExpr
  ...

-- Constructing the transform --
