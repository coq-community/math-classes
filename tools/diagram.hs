{-# LANGUAGE PatternGuards #-}

{-

Introduction

  This script visualizes a proof state by scanning the context for categorical entities (categories, objects, arrows, functors) and drawing them in a diagram.

Usage

  First, insert the word "diagram" on a line of its own at the position in the proof where you want the context to be visualized.

  Next, if the following is your normal coq{c,top,ide} invocation:

    coq{c,top,ide} -bunch -of -flags path/to/file.v

  then the following command draws the diagram:

    runhaskell tools/diagram.hs -bunch -of -flags path/to/file.v | dot -Tpng > t.png

Limitations

  We cannot always spot all categories and functors because we do not have canonical names for object types and object maps, and the Category/Functor instances are not always visible.

  Names of things can get rather ugly because the diagrams are based on the output of [Set Printing All]. We currently define some ad-hoc implicit arguments and notations for things like fst/proj1_sig/comp.

  The whole thing is little more than a proof of concept at this point.

-}

import Text.ParserCombinators.Parsec
import Control.Monad (liftM2)
import Data.Monoid
import Data.Function (fix)
import Data.Maybe (mapMaybe, listToMaybe)
import Data.HashTable (hashString)
import Data.List (nub, intersperse, find, isSuffixOf)
import System.IO.UTF8 (putStr)
import Data.Char (isSpace)
import qualified Data.Set as Set
import Data.Set (Set)
import Prelude hiding ((++), (.), putStr)
import System (getArgs)
import System.Process (readProcessWithExitCode)

-- Utility:

(.) :: Functor f => (a -> b) -> (f a -> f b)
(.) = fmap

mconcatMap :: Monoid m => (a -> m) -> [a] -> m
mconcatMap f l = mconcat $ map f l

(++) :: Monoid a => a -> a -> a
(++) = mappend

(<<) :: Monad m => m b -> m a -> m b
x << y = do r <- x; y; return r

findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
findMaybe f = listToMaybe . mapMaybe f

-- Data types:

data Expr = Id String | Op String [Expr] | Expr :* Expr deriving (Eq, Ord)
data Functor' = Functor' { functor_term :: Expr, functor_from, functor_to :: Category } deriving (Eq, Show)
data Category = Category { cat_term :: Expr } deriving (Eq, Show)
data Object = Object { obj_term :: Expr, obj_cat :: Category } deriving (Eq, Show)
data Arrow = Arrow { arrow_term :: Expr, arrow_from, arrow_to :: Object } deriving (Eq, Show)
data Equality = Equality { eq_left, eq_right :: Arrow } deriving (Eq, Show)

-- Display:

instance Show Expr where show = show_expr False . clean_expr

clean_expr :: Expr -> Expr
clean_expr (Id "@comp" :* _ :* _ :* _ :* _ :* _ :* _ :* a :* b) = Op " ∘ " [clean_expr a, clean_expr b]
clean_expr (Id "@fmap" :* _ :* _ :* _ :* _ :* n :* _ :* _ :* _ :* a) = clean_expr n :* clean_expr a
clean_expr (Id "@fst" :* _ :* _) = Id "fst"
clean_expr (Id "@snd" :* _ :* _) = Id "snd"
clean_expr (Id "@proj1_sig" :* _ :* _ :* x) = x
clean_expr (Id "@cat_id" :* _ :* _ :* _ :* _) = Id "id"

clean_expr (Id "@map_obj" :* _ :* _ :* x) = x

clean_expr t | Just (_, from, to) <- is_arrow_expr t = Op " -> " [clean_expr from, clean_expr to]
clean_expr (x :* y) = clean_expr x :* clean_expr y
clean_expr (Op o l) = Op o (map clean_expr l)
clean_expr (Id x) = Id x

show_expr :: Bool -> Expr -> String
show_expr _ (Id s) = s
show_expr nested (Op o l) =
  (if nested then \x -> "(" ++ x ++ ")" else id) $
  concat (intersperse o (map (show_expr False) l))
show_expr nested (x :* y) =
  (if nested then \x -> "(" ++ x ++ ")" else id) $
  show_expr True x ++ " " ++ show_expr True y

-- Parsing lines:

line_conts :: [String] -> [String]
line_conts = go ""
  where
    go :: String -> [String] -> [String]
    go cur []
      | all isSpace cur = []
      | otherwise = [cur]
    go cur (x@(' ':_) : xs) = go (cur ++ x) xs
    go cur (x:xs) = (if all isSpace cur then id else (cur :)) (go x xs)

idchar :: GenParser Char st Char
idchar = oneOf "@_'.:=>" <|> alphaNum

app :: CharParser st Expr
app = fmap (foldl1 (:*)) $ flip sepBy1 spaces $
  (char '(' >> app << char ')') <|>
  fmap Id (many1 idchar)
  
line :: CharParser st (String, Expr)
line = liftM2 (,) (many1 idchar) (string " : " >> app)

raw_to_decl :: String -> Maybe (String, Expr)
raw_to_decl s
  | Right r <- parse line "" s = Just r
  | otherwise = Nothing

-- Getting data from parsed lines:

is_arrow_expr :: Expr -> Maybe (Expr, Expr, Expr)
is_arrow_expr e
  | Just (Object o (Category c), Object o' _) <- is_arrow_type e = Just (c, o, o')
  | otherwise = Nothing

is_arrow_type :: Expr -> Maybe (Object, Object)
is_arrow_type (Id n :* cat :* _ :* from :* to) | n `elem` arr = Just (Object from (Category cat), Object to (Category cat))
  where arr = ["@Arrow", "@canonical_names.Arrow"]
is_arrow_type _ = Nothing

decl_to_datum :: (String, Expr) -> ([Category], [Object], [Arrow], [Equality], [Functor'])
decl_to_datum (name, t) | Just (cat, from, to) <- is_arrow_expr t
  = no_eqs $ expand $ Arrow (Id name) (Object from (Category cat)) (Object to (Category cat))
decl_to_datum (_, Id "@Category" :* cat :* _ :* _ :* _ :* _) = no_eqs $ expand $ Category cat
decl_to_datum (_, Id "@Functor" :* cat :* _ :* _ :* _ :* _ :* cat' :* _ :* _ :* _ :* _ :* n :* _) =
  ([], [], [], [], [Functor' n (Category cat) (Category cat')]) ++ no_eqs (expand n ++ expand (Category cat) ++ expand (Category cat'))

decl_to_datum (_, Id "@equiv" :* t :* _ :* a :* b) | Just (cat, from, to) <- is_arrow_expr t
  = let c' = Category cat; from' = Object from c'; to' = Object to c'; a' = Arrow a from' to'; b' = Arrow b from' to' in
    ([], [], [], [Equality a' b'], []) ++ no_eqs (expand a' ++ expand b')
decl_to_datum _ = mempty

no_eqs :: ([Category], [Object], [Arrow], [Functor']) -> ([Category], [Object], [Arrow], [Equality], [Functor'])
no_eqs (x, y, z, u) = (x, y, z, [], u)

class Expand t where expand :: t -> ([Category], [Object], [Arrow], [Functor'])

instance Expand Expr where
  expand (Id _) = mempty
  expand (Op _ _) = undefined
  expand e@(x :* y) = expand x ++ expand y ++ (
    case e of
      Id "@comp" :* cat :* _ :* _ :* x :* y :* z :* a :* b ->
        let c' = Category cat; x' = Object x c'; y' = Object y c'; z' = Object z c' in
          ([], [], [Arrow e x' z'], []) ++ expand (Arrow a y' z') ++ expand (Arrow b x' y')
      Id "@fmap" :* cat :* _ :* cat' :* _ :* e :* _ :* o :* o' :* a ->
        -- todo: shouldn't we add the fmapped arrow itself?
        ([], [], [], [Functor' e (Category cat) (Category cat')]) ++
        expand (Arrow a (Object o (Category cat)) (Object o' (Category cat)))
      Id "@cat_id" :* cat :* _ :* _ :* o -> expand (Object o (Category cat))
      _ -> mempty)

instance Expand Equality where
  expand (Equality a b) = expand a ++ expand b
instance Expand Category where
  expand c@(Category e) = expand e ++ ([c], [], [], [])
instance Expand Object where
  expand o@(Object e c) = expand e ++ expand c ++ ([], [o], [], [])
instance Expand Arrow where
  expand a@(Arrow e from to) = expand e ++ expand from ++ expand to ++ ([], [], [a], [])

-- Treating equalities

classes :: Ord a => [(a, a)] -> [Set a]
classes = foldr add []
 where
  add (x, y) = fix $ \rec l -> case l of
    [] -> [Set.fromList [x, y]]
    s:ss
      | Set.member x s -> Set.insert y s : ss
      | Set.member y s -> Set.insert x s : ss
      | otherwise -> s : rec ss

merge :: [Arrow] -> Set Expr -> [Arrow]
merge l s = map f l
  where
    f (Arrow n from to) = Arrow (if Set.member n s then e else n) from to
    e = Op "\\n= " (Set.toList s)

process_equalities :: ([Category], [Object], [Arrow], [Equality], [Functor']) -> ([Category], [Object], [Arrow], [Functor'])
process_equalities (cats, objs, arrows, eqs, funcs) =
  (cats, objs, foldl merge arrows (classes $ map (\(Equality (Arrow x _ _) (Arrow y _ _)) -> (x, y)) eqs), funcs)

-- Conversion to dot:

h :: Show a => a -> String
h = show . abs . hashString . show

arrow_to_dot :: Arrow -> String
arrow_to_dot (Arrow name (Object from _) (Object to _)) =
  h from ++ " -> " ++ h to ++ " [label=\"" ++ show name ++ "\"]"

category_to_dot :: Category -> String
category_to_dot (Category c) = "subgraph cluster" ++ h c ++ " { label = \"" ++ show c ++ "\" }"

object_to_dot :: [Functor'] -> [Object] -> Object -> String
object_to_dot funcs objs (Object o (Category c)) =
  "subgraph cluster" ++ h c ++ " { " ++ h o ++ "[label=\"" ++ show o ++ "\"] }" ++
  case o of
    (x :* y) | x `elem` map functor_term funcs ->
      "\n" ++ h y ++ " -> " ++ h o ++ " [label=\"" ++ show x ++ "\", style=dashed]"
    (x :* y) | y `elem` map obj_term objs ->
      "\n" ++ h y ++ " -> " ++ h o ++ " [label=\"" ++ show x ++ "\", style=dashed]"
        -- This is a bit forward, because it's saying that whenever an object is named "x y" where y also happens to be an object, we draw a dashed arrow from y to "x y" with label x, under the assumption that x is some sort of map (not necessary a functor).
    _ -> ""

-- Putting it all together:

main :: IO ()
main = do
  args <- getArgs
  let (flags, source_file) = (init args, last args)
  source <- unlines . (++ ["Set Printing All.", "Show."]) . takeWhile (not . (== "diagram")) . lines . readFile source_file
  (result, out, _) <- readProcessWithExitCode "coqtop" flags source
  -- todo: assert that result == ExitSuccess
  putStr
    $ unlines
    $ (\x -> ["digraph {"] ++ x ++ ["}"])
    $ (\(x, objs, z, funcs) -> map category_to_dot x ++ map (object_to_dot funcs objs) objs ++ map arrow_to_dot z)
    $ (\(x, y, z, d) -> (nub x, nub y, nub z, nub d))
    $ process_equalities
    $ mconcatMap decl_to_datum
    $ mapMaybe raw_to_decl
    $ line_conts
    $ map (\(' ':' ':x) -> x) -- remove indentation
    $ takeWhile (not . (== "  ============================"))
    $ drop 1 -- empty line after "# subgoal(s)"
    $ reverse
    $ takeWhile (\x -> not $ " subgoals" `isSuffixOf` x || " subgoal" `isSuffixOf` x)
    $ reverse
    $ lines
    $ out

