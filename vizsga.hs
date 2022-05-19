{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

import Control.Applicative
import Control.Monad
import Data.Char
import Data.Maybe
import Data.Either
import Data.Foldable

-- State monad
--------------------------------------------------------------------------------

newtype State s a = State {runState :: s -> (a, s)}
  deriving Functor

instance Applicative (State s) where
  pure  = return
  (<*>) = ap

instance Monad (State s) where
  return a = State $ \s -> (a, s)
  State f >>= g = State $ \s -> case f s of
    (a, s') -> runState (g a) s'

get :: State s s
get = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ \_ -> ((), s)

modify :: (s -> s) -> State s ()
modify f = get >>= \s -> put (f s)

evalState :: State s a -> s -> a
evalState ma = fst . runState ma

execState :: State s a -> s -> s
execState ma = snd . runState ma

--------------------------------------------------------------------------------
--                              Feladatok
--------------------------------------------------------------------------------

data MaybeTree a
  = Node (MaybeTree a) (Maybe a) (MaybeTree a)
  | Leaf a
  deriving (Show)

mt :: MaybeTree Int
mt =
  Node
    (Node
      (Node (Leaf 2) Nothing (Leaf 4))
      (Nothing)
      (Leaf 10)
    )
    (Just 7)
    (Node (Leaf 0) (Just 5) (Leaf 3))

{-
          7
         / \
        /   \
       /     \
      /\      5
     /  10   / \
    /\      0   3
   2  4
-}

mt' :: MaybeTree (Either Bool Char)
mt' =
  Node
    (Node
      (Leaf $ Right 'a')
      (Nothing)
      (Node (Leaf $ Left True) Nothing (Leaf $ Right 'b')
      )
    )
    (Just $ Right 'c')
    (Node (Leaf $ Left False) Nothing (Leaf $ Left True))


instance (Eq a) => Eq (MaybeTree a) where
  (Leaf a) == (Leaf b) = a == b
  (Node a b c) == (Node x y z) = a == x && b == y && c == z
  _ == _ = False 

instance Functor MaybeTree where
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Node a b c) = case b of
      Just x  -> Node (fmap f a) (Just $ f x) (fmap f c)
      Nothing -> Node (fmap f a) Nothing (fmap f c)

instance Foldable MaybeTree where
  foldr f def (Leaf a) = f a def
  foldr f def (Node a b c) = foldr f (foldr f (foldr f def c) b) a

instance Traversable MaybeTree where
  traverse f (Leaf a) = Leaf <$> f a
  traverse f (Node a b c) = case b of
      Just x  -> (\ x y z -> Node x (Just y) z) <$> traverse f a <*> f x <*> traverse f c
      Nothing -> Node <$> traverse f a <*> pure Nothing <*> traverse f c

mirror :: MaybeTree a -> MaybeTree a
mirror (Leaf a) = Leaf a
mirror (Node a b c) = Node (mirror c) b (mirror a)


countNothings :: MaybeTree a -> Int
countNothings (Leaf a) = 0
countNothings (Node a b c) = countNothings a + (if isNothing b then 1 else 0) + countNothings c

alternateSigns :: MaybeTree Int -> MaybeTree Int
alternateSigns tree = evalState (signState tree) False
    where
        signState :: MaybeTree Int -> State Bool (MaybeTree Int)
        signState (Leaf a) = do
            p <- get
            modify not
            a' <- if p then pure $ a * (-1) else pure a
            pure $ Leaf a'

        signState (Node a b c) = do
            x <- signState a
            p <- get
            modify (\e -> if isNothing b then e else not e)
            y <- case b of
                Nothing -> pure Nothing
                Just a  -> if p then pure $ Just $ a * (-1) else pure $ Just a
            z <- signState c
            pure (Node x y z)

            



bools :: MaybeTree (Either Bool Char) -> [Bool]
bools (Node a b c) = case b of
    Just (Left b) -> bools a ++ (b:bools c)
    _             -> bools a ++ bools c

bools (Leaf a) = case a of
    Left b -> [b]
    _ -> [] 


lastChar :: MaybeTree (Either Bool Char) -> Maybe Char
lastChar = foldr f Nothing
    where
        f :: Either Bool Char -> Maybe Char -> Maybe Char
        f (Right ch) Nothing    = Just ch
        f (Left _)   x          = x
        f _          (Just ch2) = Just ch2
        

--------------------------------------------------------------------------------
--                  While nyelv parser + interpreter
--------------------------------------------------------------------------------

newtype Parser a = Parser {runParser :: String -> Maybe (a, String)}
  deriving Functor

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Monad Parser where
  return a = Parser $ \s -> Just (a, s)
  Parser f >>= g = Parser $ \s ->
    case f s of
      Nothing     -> Nothing
      Just(a, s') -> runParser (g a) s'

instance Alternative Parser where
  empty = Parser $ \_ -> Nothing
  (<|>) (Parser f) (Parser g) = Parser $ \s -> case f s of
    Nothing -> g s
    x       -> x

satisfy :: (Char -> Bool) -> Parser Char
satisfy f = Parser $ \s -> case s of
  c:cs | f c -> Just (c, cs)
  _          -> Nothing

eof :: Parser ()
eof = Parser $ \s -> case s of
  [] -> Just ((), [])
  _  -> Nothing

char :: Char -> Parser ()
char c = () <$ satisfy (==c)

string :: String -> Parser ()
string = mapM_ char

ws :: Parser ()
ws = () <$ many (char ' ' <|> char '\n')

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 pa pb = (:) <$> pa <*> many (pb *> pa)

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy pa pb = sepBy1 pa pb <|> pure []

anyChar :: Parser Char
anyChar = satisfy (const True)

-- While nyelv
------------------------------------------------------------

data Exp
  = Add Exp Exp    -- a + b
  | Mul Exp Exp    -- a * b
  | Var Name       -- x
  | IntLit Int
  | BoolLit Bool   -- true|false
  | Not Exp        -- not e
  | And Exp Exp    -- a && b
  | Or Exp Exp     -- a || b
  | Eq Exp Exp     -- a == b
  | Lt Exp Exp     -- a < b
  | XOr Exp Exp
  deriving (Eq, Show)

type Program = [Statement]
type Name    = String

data Statement
  = Assign Name Exp         -- x := e
  | While Exp Program       -- while e do p1 end
  | If Exp Program Program  -- if e then p1 else p2 end
  | Block Program           -- {p1}  (lokális scope)
  | Loop Exp Program
  deriving (Eq, Show)


-- While parser
--------------------------------------------------------------------------------

{-
Parser a While nyelvhez. A szintaxist az Exp és Statement definíciónál látahtó
fenti kommentek összegzik, továbbá:

  - mindenhol lehet whitespace tokenek között
  - a Statement-eket egy Program-ban válassza el ';'
  - Az operátorok erőssége és assszociativitása a következő (csökkenő erősségi sorrendben):
      *  (bal asszoc)
      +  (bal asszoc)
      <  (nem asszoc)
      == (nem asszoc)
      && (jobb asszoc)
      || (jobb asszoc)
  - "not" erősebben köt minden operátornál.
  - A kulcsszavak: not, and, while, do, if, end, true, false.
  - A változónevek legyenek betűk olyan nemüres sorozatai, amelyek *nem* kulcsszavak.
    Pl. "while" nem azonosító, viszont "whilefoo" már az!

Példa szintaktikilag helyes programra:

  x := 10;
  y := x * x + 10;
  while (x == 0) do
    x := x + 1;
    b := true && false || not true
  end;
  z := x
-}

char' :: Char -> Parser ()
char' c = char c <* ws

string' :: String -> Parser ()
string' s = string s <* ws

keywords :: [String]
keywords = ["not", "and", "while", "do", "if", "end", "true", "false", "loop", "times"]

pIdent :: Parser String
pIdent = do
  x <- some (satisfy isLetter) <* ws
  if elem x keywords
    then empty
    else pure x

pKeyword :: String -> Parser ()
pKeyword str = do
  string str
  mc <- optional (satisfy isLetter)
  case mc of
    Nothing -> ws
    Just _  -> empty

pBoolLit :: Parser Bool
pBoolLit = (True  <$ pKeyword "true")
       <|> (False <$ pKeyword "false")

pIntLit :: Parser Int
pIntLit = read <$> (some (satisfy isDigit) <* ws)

pAtom :: Parser Exp
pAtom = (BoolLit <$> pBoolLit)
      <|> (IntLit <$> pIntLit)
      <|> (Var <$> pIdent)
      <|> (char' '(' *> pExp <* char' ')')

pNot :: Parser Exp
pNot =
      (Not <$> (pKeyword "not" *> pAtom))
  <|> pAtom

pMul :: Parser Exp
pMul = foldl1 Mul <$> sepBy1 pNot (char' '*')

pAdd :: Parser Exp
pAdd = foldl1 Add <$> sepBy1 pMul (char' '+')

pLt :: Parser Exp
pLt = do
  e <- pAdd
  (Lt e <$> (string' "<"  *> pAdd)) <|> pure e

pEq :: Parser Exp
pEq = do
  e <- pLt
  (Eq e <$> (string' "==" *> pLt)) <|> pure e

pAnd :: Parser Exp
pAnd = foldr1 And <$> sepBy1 pEq (string' "&&")

pXor :: Parser Exp
pXor = foldr1 XOr <$> sepBy1 pAnd (string' "^^")

pOr :: Parser Exp
pOr = foldr1 Or <$> sepBy1 pXor (string' "||")

pExp :: Parser Exp
pExp = pOr

pProgram :: Parser Program
pProgram = sepBy pStatement (char' ';')

pStatement :: Parser Statement
pStatement =
        (Assign <$> pIdent <*> (string' ":=" *> pExp))
    <|> (While <$> (pKeyword "while" *> pExp)
               <*> (pKeyword "do" *> pProgram <* pKeyword "end"))
    <|> (If <$> (pKeyword "if"   *> pExp)
            <*> (pKeyword "then" *> pProgram)
            <*> (pKeyword "else" *> pProgram <* pKeyword "end"))
    <|> (Block <$> (char' '{' *> pProgram <* char' '}'))
    <|> (Loop <$> (pKeyword "loop" *> pExp) <*> (pKeyword "times" *> pProgram <* pKeyword "end"))

pSrc :: Parser Program
pSrc = ws *> pProgram <* eof

-- Interpreter
------------------------------------------------------------

{-
Interpreter a While nyelvhez.

Kifejezések:
  - A logikai és artimetikai műveletek kiértékelése értelemszerű. Ha nem
    megfelelő típusú értéket kapunk argumentumokra, dobjunk "error"-al hibát.
  - Az == operátor működik, ha mindkét argumentum Bool, vagy ha mindkét argumentum
    Int, az eredmény mindig Bool.

Változó scope és értékadás kezelése:
  - Új scope-nak számít:
    - minden "while" kifejezés teste
    - minden "if" kifejezés két ága
    - minden új Block (a szintaxisban pl "x := 0; {y := x; x := x}"-nél
      a kapcsos zárójeles utasítássorozat új blokkban van).

  - ha egy új változónak értéket adunk, akkor felvesszük a környezet elejére
  - ha egy meglévő változónak értéket adunk, akkor update-eljük a változó értékét
  - amikor az interpreter végez egy scope kiértékeléséval, eldobja az összes,
    scope-ban újonnan felvett változót a környezetből.
-}

type Val  = Either Int Bool
type Env  = [(Name, Val)]
type Eval = State Env

evalExp :: Exp -> Eval Val
evalExp e = case e of
  Add e1 e2 -> do
    v1 <- evalExp e1
    v2 <- evalExp e2
    case (v1, v2) of
      (Left n1, Left n2) -> pure (Left (n1 + n2))
      _                  -> error "type error in + argument"
  Mul e1 e2 -> do
    v1 <- evalExp e1
    v2 <- evalExp e2
    case (v1, v2) of
      (Left n1, Left n2) -> pure (Left (n1 * n2))
      _                  -> error "type error in * argument"
  Or e1 e2 -> do
    v1 <- evalExp e1
    v2 <- evalExp e2
    case (v1, v2) of
      (Right b1, Right b2) -> pure (Right (b1 || b2))
      _                    -> error "type error in || argument"
  And e1 e2 -> do
    v1 <- evalExp e1
    v2 <- evalExp e2
    case (v1, v2) of
      (Right b1, Right b2) -> pure (Right (b1 && b2))
      _                    -> error "type error in && argument"
  Eq  e1 e2 -> do
    v1 <- evalExp e1
    v2 <- evalExp e2
    case (v1, v2) of
      (Left  n1, Left  n2) -> pure (Right (n1 == n2))
      (Right b1, Right b2) -> pure (Right (b1 == b2))
      _                    -> error "type error in == arguments"
  Lt  e1 e2 -> do
    v1 <- evalExp e1
    v2 <- evalExp e2
    case (v1, v2) of
      (Left  n1, Left  n2) -> pure (Right (n1 < n2))
      _                    -> error "type error in < arguments"
  Var x -> do
    env <- get
    case lookup x env of
      Nothing -> error ("variable not in scope: " ++ x)
      Just v  -> pure v
  IntLit n ->
    pure (Left n)
  BoolLit b ->
    pure (Right b)
  Not e -> do
    v <- evalExp e
    case v of
      Right b -> pure (Right (not b))
      _       -> error "type error in \"not\" argument"
  XOr exp1 exp2 -> do
      x <- evalExp exp1
      y <- evalExp exp2

      case (x, y) of
          (Right a, Right b) -> pure $ Right (xor a b)
            where
                xor :: Bool -> Bool -> Bool
                xor x y = (x || y) && not (x && y)
          _ -> error "type error in xor"

newScope :: Eval a -> Eval a
newScope ma = do
  env <- (get :: State Env Env)
  a <- ma
  modify (\env' -> drop (length env' - length env) env')
  pure a

updateEnv :: Name -> Val -> Env -> Env
updateEnv x v env =
  case go env of
    Nothing   -> (x, v):env
    Just env' -> env'
  where
    go :: Env -> Maybe Env
    go [] = Nothing
    go ((x', v'):env)
      | x == x'   = Just ((x, v):env)
      | otherwise = ((x', v'):) <$> go env

evalSt :: Statement -> Eval ()
evalSt s = case s of
  Assign x e -> do
    v <- evalExp e
    modify (updateEnv x v)
  While e p -> do
    v <- evalExp e
    case v of
      Right b -> if b then newScope (evalProg p) >> evalSt (While e p)
                      else pure ()
      Left _  -> error "type error: expected a Bool condition in \"while\" expression"
  If e p1 p2 -> do
    v <- evalExp e
    case v of
      Right b -> if b then newScope (evalProg p1)
                      else newScope (evalProg p2)
      Left _ -> error "type error: expected a Bool condition in \"if\" expression"
  Block p ->
    newScope (evalProg p)

  Loop exp prog -> do
      x <- evalExp exp
      case x of
          Left n -> replicateM_ n (newScope (evalProg prog))
          _      -> error "type error: expected an Int expression in loop"

evalProg :: Program -> Eval ()
evalProg = mapM_ evalSt


-- interpreter
--------------------------------------------------------------------------------

runProg :: String -> Env
runProg str = case runParser pSrc str of
  Nothing     -> error "parse error"
  Just (p, _) -> execState (evalProg p) []

p1 :: String
p1 = "x := 10; y := 20; {z := x + y}; x := x + 100"

p2 :: String
p2 = unwords
  [ "x := 5;"
  , "y := 1;"
  , "z := 1;"
  , "loop x times"
  , "z := z * y;"
  , "y := y + 1"
  , "end"
  ]

p3 :: String
p3 = unwords
  [ "x := 0;"
  , "loop 5 times"
  , "i := x * 2;"
  , "x := i + 1"
  , "end"
  ]

p4 :: String
p4 = unwords
  [ "x := 3;"
  , "y := 0;"
  , "while (x < 15 ^^ 10 < y) do"
  , "x := x * 2;"
  , "y := y + 3"
  , "end"
  ]