{-# LANGUAGE PatternGuards #-}

import Data.List (nub, (\\))
import Data.Map (Map)
import qualified Data.Map as Map

none :: (a -> Bool) -> [a] -> Bool
none p = all (not . p)

hide :: [String]
hide = words "util c_util list_util"

main :: IO ()
main = interact $ \s ->
  let
    reported_deps_map :: Map String [String]
    reported_deps_map = Map.fromList $ map parse_line $ lines s

    reported_deps :: String -> [String]
    reported_deps n = Map.findWithDefault [] n reported_deps_map

    names :: [String]
    names = Map.keys reported_deps_map \\ hide

    deep_deps_map :: Map String [String]
    deep_deps_map = Map.fromList $ map (\n -> (n, let r = reported_deps n in r ++ concatMap deep_deps r)) names

    deep_deps :: String -> [String]
    deep_deps n = Map.findWithDefault [] n deep_deps_map

    all_deps = concatMap (\n -> map (\d -> (n, d)) (deep_deps n)) names
    depends_on x y = y `elem` deep_deps x
    deps = [(x, y) | (x, y) <- all_deps, none (\n -> x `depends_on` n && n `depends_on` y) (names \\ [x, y])]
  in
    unlines $ ["digraph {"] ++ map (\(x, y) -> "\"" ++ x ++ "\" -> \"" ++ y ++ "\"") deps ++ ["}"]
 where
  parse_line :: String -> (String, [String])
  parse_line l | (x, (_:xs)) <- span (/= ':') l = (strip_suffix x, map strip_suffix (tail $ words xs) \\ hide)
  strip_suffix = takeWhile (/= '.')
