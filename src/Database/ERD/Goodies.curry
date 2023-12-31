------------------------------------------------------------------------------
--- This module contains some useful operations on the data types representing
--- entity/relationship diagrams
---
--- @author Michael Hanus
--- @version December 2021
------------------------------------------------------------------------------
{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

module Database.ERD.Goodies
  ( erdName, entityName, isEntityNamed, entityAttributes
  , hasForeignKey, foreignKeyAttributes
  , attributeName, attributeDomain, hasDefault
  , isForeignKey, isNullAttribute
  , cardMinimum, cardMaximum
  , showERD, combineIds
  , readERDFromProgram, storeERDFromProgram
  ) where

import Curry.Compiler.Distribution ( installDir )
import Data.Char                   ( isUpper )
import Data.List                   ( intersperse )
import Data.Maybe
import System.Environment          ( getEnv )

import Database.ERD
import FlatCurry.Types
import FlatCurry.Files
import FlatCurry.Goodies
import System.CurryPath    ( runModuleActionQuiet, stripCurrySuffix )
import System.Directory    ( getAbsolutePath, removeFile )
import System.FilePath     ( (</>) )
import System.IOExts       ( evalCmd, readCompleteFile )
import System.Process      ( getPID, system )


--- The name of an ERD.
erdName :: ERD -> String
erdName (ERD name _ _) = name

--- The name of an entity.
entityName :: Entity -> String
entityName (Entity n _) = n

--- Is this an entity with a given name?
isEntityNamed :: String -> Entity -> Bool
isEntityNamed n e = entityName e == n

--- Has the entity an attribute with a foreign key for a given entity name?
hasForeignKey :: String -> Entity -> Bool
hasForeignKey ename (Entity _ attrs) = any isForeignKeyWithName attrs
 where
  isForeignKeyWithName (Attribute _ d _ _) = case d of KeyDom n -> n==ename
                                                       _        -> False

--- Returns the attributes that are a foreign key of a given entity name.
foreignKeyAttributes :: String -> [Attribute] -> [Attribute]
foreignKeyAttributes ename attrs = filter isForeignKeyWithName attrs
 where
  isForeignKeyWithName (Attribute _ d _ _) = case d of KeyDom n -> n==ename
                                                       _        -> False

--- Returns the names of the foreign key attributes for a given entity name.
foreignKeyAttrNames :: String -> [Attribute] -> [String]
foreignKeyAttrNames ename attrs =
  map attributeName (filter isForeignKeyWithName attrs)
 where
  isForeignKeyWithName (Attribute _ d _ _) = case d of KeyDom n -> n==ename
                                                       _        -> False

--- The attributes of an entity
entityAttributes :: Entity -> [Attribute]
entityAttributes (Entity _ attrs) = attrs

--- The name of an attribute.
attributeName :: Attribute -> String
attributeName (Attribute name _ _ _) = name

--- The domain of an attribute.
attributeDomain :: Attribute -> Domain
attributeDomain (Attribute _ d _ _) = d

--- Has an attribute domain a default value?
hasDefault :: Domain -> Bool
hasDefault (IntDom    d) = isJust d
hasDefault (FloatDom  d) = isJust d
hasDefault (StringDom d) = isJust d
hasDefault (BoolDom   d) = isJust d
hasDefault (DateDom   d) = isJust d
hasDefault (UserDefined _ d) = isJust d

---- Is an attribute a (generated) foreign key?
isForeignKey :: Attribute -> Bool
isForeignKey (Attribute _ d _ _) = case d of KeyDom _ -> True
                                             _        -> False
           
--- Has an attribute a null value?
isNullAttribute :: Attribute -> Bool
isNullAttribute (Attribute _ _ _ isnull) = isnull
           
--- The minimum value of a cardinality.
cardMinimum :: Cardinality -> Int
cardMinimum (Exactly i) = i
cardMinimum (Between i _) = i

--- The maximum value of a cardinality (provided that it is not infinite).
cardMaximum :: Cardinality -> Int
cardMaximum (Exactly i) = i
cardMaximum (Between _ (Max i)) = i


--- A simple pretty printer for ERDs.
showERD :: Int -> ERD -> String
showERD n (ERD en es rs) = "ERD " ++ showString en ++ lb n ++
  " [" ++ concat (intersperse ("," ++ lb (n+2)) (map (showEs (n+2)) es)) ++ "]"
  ++ lb n ++
  " [" ++ concat (intersperse ("," ++ lb (n+2)) (map (showRs (n+2)) rs)) ++ "]"

showEs :: Int -> Entity -> String
showEs n (Entity en attrs) = "Entity " ++ showString en ++ lb (n+7) ++
  "[" ++ concat (intersperse ("," ++ lb (n+8)) (map showWOBrackets attrs)) ++"]"

showRs :: Int -> Relationship -> String
showRs n (Relationship rn ends) =
  "Relationship " ++ showString rn ++ lb (n+13) ++
  "[" ++ concat (intersperse ("," ++ lb (n+14)) (map showWOBrackets ends)) ++"]"

showWOBrackets :: Show a => a -> String
showWOBrackets t = stripBrackets (show t)
 where
  stripBrackets (c:cs) = if c=='(' then reverse (tail (reverse cs)) else c:cs

showString :: String -> String
showString s = "\"" ++ s ++ "\""

lb :: Int -> String
lb n = "\n" ++ take n (repeat ' ')


--- Combines a non-empty list of identifiers into a single identifier.
--- Used in ERD transformation and code generation to create
--- names for combined objects, e.g., relationships and foreign keys.
combineIds :: [String] -> String
combineIds (name:names) = name ++ concatMap maybeAddUnderscore names
 where
  maybeAddUnderscore [] = "_"
  maybeAddUnderscore s@(c:_) = if isUpper c then s else '_' : s

------------------------------------------------------------------------------
-- Auxiliaries to read ERD definition given in a Curry program.

--- Reads the ERD defined in a Curry program (as a top-level operation
--- of type `Database.ERD.ERD`).
--- This is done by compiling the Curry program with an auxiliary
--- operation and processing the output of the program.
readERDFromProgram :: String -> IO ERD
readERDFromProgram progfile = do
  putStr $ "Processing ERD in program `" ++ progfile ++ "'..."
  let progname = stripCurrySuffix progfile
  prog <- runModuleActionQuiet readFlatCurry progname
  let funcs = progFuncs prog
      erdfuncs = filter hasERDType funcs
  case erdfuncs of
    []   -> error $ "No definition of ER model found in program " ++ progfile
    [fd] -> do currypath <- getEnv "CURRYPATH"
               pid <- getPID
               let tmpfile = "/tmp/ERD2CURRY_tmp_" ++ show pid
               let cmd = installDir </> "bin" </> "curry"
                   args  = [ "--nocypm"
                           , ":set","v0" ]
                   input = unlines $
                            (if null currypath
                               then []
                               else [":set path " ++ currypath] ) ++
                            [ ":load " ++ progname
                            , ":add " ++ "Database.ERD"
                            , ":eval writeFileWithERDTerm " ++
                                     show tmpfile ++ snd (funcName fd)
                            , ":quit"]
               (ecode,_,errstr) <- evalCmd cmd args input
               putStrLn "done"
               if ecode > 0
                 then error $ "ERROR in program defining ERD:\n" ++ errstr
                 else do erdtermfile <- readCompleteFile tmpfile
                         removeFile tmpfile
                         return (read erdtermfile)
    _ -> error $ "Multiple ER model definitions found in program " ++ progfile

--- Writes the ERD defined in a Curry program (as a top-level operation
--- of type `Database.ERD.ERD`) in a term file and return the name of
--- the term file.
storeERDFromProgram :: String -> IO String
storeERDFromProgram progfile = do
  erd <- readERDFromProgram progfile
  fname <- writeERDTermFile erd
  putStrLn $ "ERD term file '" ++ fname ++ "' written."
  return fname

hasERDType :: FuncDecl -> Bool
hasERDType fdecl = funcType fdecl == TCons ("Database.ERD","ERD") []

------------------------------------------------------------------------------
