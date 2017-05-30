--- ----------------------------------------------------------------------------
--- This module creates all datatypes to represent the entities and
--- relations of a relational (SQLite) database corresponding to a
--- logical ER model specified in a file `x_ERDT.term` (which is
--- a transformed ER-Model that was translated by erd2curry).
--- It produces a Curry program `x_CDBI.curry` and a file
--- `x_SQLCODE.info` that is used when embedded SQL statements are
--- translated by the Curry preprocessor `currypp`.
---
--- @author Mike Tallarek, extensions by Julia Krone and Michael Hanus
--- @version 0.2
--- ----------------------------------------------------------------------------

{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

import AbstractCurry.Types
import AbstractCurry.Pretty
import AbstractCurry.Build

import Char           ( toLower, toUpper )
import Database.ERD
import Directory      ( doesFileExist, getAbsolutePath )
import Distribution   ( installDir )
import qualified FilePath as FP ( (</>), combine, splitFileName)
import IO
import IOExts         ( connectToCommand )
import List
import Pretty
import ReadShowTerm   ( readsQTerm )
import SetFunctions   ( selectValue, set2 )
import System
import Time

import Database.ERD.Goodies

-- Write all the data so CDBI can be used, create a database (if it does
-- not exist) and a .info file/
-- The parameters are the name of the file containing the ERD term,
-- the ER model, and the name of the SQLite3 database.
writeCDBI :: String -> ERD -> String -> IO ()
writeCDBI erdfname (ERD name ents rels) dbname = do
  dbPath <- getAbsolutePath dbname
  let cdbiMod  = name++"_CDBI"
      cdbiFile = cdbiMod++".curry"
      imports = [ "Time"
                , "Database.CDBI.ER"
                , "Database.CDBI.Criteria"
                , "Database.CDBI.Connection"
                , "Database.CDBI.Description"]
      typeDecls = foldr ((++) . (getEntityTypeDecls cdbiMod)) [] ents 
      funcDecls = genDBPathFunc cdbiMod dbPath :
                  foldr ((++) . (getEntityFuncDecls cdbiMod)) [] ents
  writeFile cdbiFile $
    "--- This file has been generated from `"++erdfname++"`\n"++
    "--- and contains definitions for all entities and relations\n"++
    "--- specified in this model.\n\n"++
    pPrint (ppCurryProg defaultOptions
                (CurryProg (name++"_CDBI") imports typeDecls funcDecls []))
  infofilehandle <- openFile (name++"_SQLCode.info") WriteMode
  writeParserFile infofilehandle name ents rels dbPath
  hClose infofilehandle
  dbexists <- doesFileExist dbPath
  if dbexists
   then do
    putStrLn $ "Database '" ++ dbPath ++ "' exists and, thus, not modified."
    putStrLn $ "Please make sure that this database is conform to the ER model!"
    -- TODO: if the database exists, check its consistency with ER model
   else do
    putStrLn $ "Creating new sqlite3 database: " ++ dbPath
    exsqlite3 <- system "which sqlite3 > /dev/null"
    when (exsqlite3>0) $
      error "Database interface `sqlite3' not found. Please install package `sqlite3'!"
    db <- connectToCommand $ "sqlite3 " ++ dbPath
    createDatabase ents db
    hClose db

genDBPathFunc :: String -> String -> CFuncDecl
genDBPathFunc mname dbPath =
  cmtfunc "The name of the SQLite database file."
          (mname,"sqliteDBFile")
          0 Public stringType [simpleRule [] (string2ac dbPath)]

-- -----writing .info-file containing auxiliary data for parsing -------------

-- Auxiliary definitions for qualified names in AbstractCurry
mDescription :: String
mDescription = "Database.CDBI.Description"

mConnection :: String
mConnection = "Database.CDBI.Connection"

--generates an AbstractCurry expression representing the parser information
-- and writes it to the file
writeParserFile :: Handle -> 
                   String -> 
                   [Entity] ->
                   [Relationship] -> 
                   String -> 
                   IO()
writeParserFile infofilehandle name ents rels dbPath = do
  hPutStrLn infofilehandle 
            (pPrint (ppCExpr defaultOptions 
                             (applyE (CSymbol ("SQLParserInfoType", "PInfo")) 
                                     [string2ac dbPath,
                                      string2ac (name++"_CDBI"),
                                      relations, 
                                      nullables,
                                      attributes,
                                      attrTypes])))  
    where relations = list2ac (foldr ((++) . (getRelationTypes ents)) [] rels)
          nullables = list2ac (foldr ((++) . (getNullableAttr)) [] ents) 
          attributes = list2ac (map getAttrList ents)
          attrTypes = list2ac (foldr ((++) . (getAttrTypes)) [] ents) 
  

-- generates data term for each  relationship 
-- depending on its type
getRelationTypes :: [Entity] -> Relationship -> [CExpr]
getRelationTypes ents rel = selectValue (set2 getrelationtypes ents rel)

-- Non-deterministic implementation:
getrelationtypes :: [Entity] -> Relationship -> [CExpr]
getrelationtypes ents (Relationship 
                       "" 
                       [REnd e1Name _ _, REnd e2Name reName _]) =                    
                           [tupleExpr [tupleExpr (map string2ac 
                                                      [e1Name, reName, 
                                                      (getCorEnt ents e1Name e2Name)]),
                                         applyE (CSymbol ("SQLParserInfoType","MtoN")) 
                                                [(string2ac e2Name)]],
                            tupleExpr [tupleExpr (map string2ac 
                                                      [e1Name, e2Name, 
                                                      (getCorEnt ents e1Name e2Name)]),
                                         applyE (CSymbol ("SQLParserInfoType","MtoN")) 
                                                 [(string2ac e2Name)]]]
getrelationtypes _ (Relationship 
                       rName 
                       [REnd e1Name re1Name (Between 0 _),
                         REnd e2Name re2Name (Exactly 1)]) =
                            [tupleExpr [tupleExpr (map string2ac 
                                                       [e2Name, re1Name, e1Name]),
                                           applyE (CSymbol ("SQLParserInfoType","OnetoN"))
                                                   [(string2ac rName)]],
                             tupleExpr [tupleExpr (map string2ac 
                                                  [e1Name, re2Name, e2Name]),
                                          applyE (CSymbol  ("SQLParserInfoType", "NtoOne")) 
                                                  [(string2ac rName)]]]  
getrelationtypes _ (Relationship 
                     rName@(_:_) 
                     [REnd e1Name re1Name (Exactly 1),
                       REnd e2Name re2Name (Between 0 _)]) = 
                          [tupleExpr [tupleExpr (map string2ac
                                                     [e2Name, re1Name, e1Name]),
                                         applyE (CSymbol ("SQLParserInfoType", "NtoOne")) 
                                                 [(string2ac rName)]],
                           tupleExpr [tupleExpr (map string2ac 
                                                     [e1Name, re2Name, e2Name]),
                                        applyE (CSymbol ("SQLParserInfoType", "OnetoN"))
                                               [(string2ac rName)]]]
getrelationtypes _ (Relationship
                      rName
                      [REnd e1Name re1Name (Between _ _),
                       REnd e2Name re2Name (Between 0 (Max 1))]) =
                          [tupleExpr [tupleExpr (map string2ac 
                                                     [e2Name, re1Name, e1Name]),
                                        applyE (CSymbol ("SQLParserInfoType", "OnetoN"))
                                               [(string2ac rName)]],
                           tupleExpr [tupleExpr (map string2ac 
                                                     [e1Name, re2Name, e2Name]),
                                        applyE (CSymbol ("SQLParserInfoType", "NtoOne"))
                                               [(string2ac rName)]]]
getrelationtypes _ (Relationship
                      rName
                      [REnd e1Name re1Name (Between 0 (Max 1)),
                       REnd e2Name re2Name (Between _ _)]) =
                          [tupleExpr [tupleExpr (map string2ac 
                                                     [e2Name, re1Name, e1Name]),
                                         applyE (CSymbol ("SQLParserInfoType", "NtoOne"))
                                                [(string2ac rName)]],
                           tupleExpr [tupleExpr (map string2ac 
                                                    [e1Name, re2Name, e2Name]),
                                       applyE (CSymbol ("SQLParserInfoType","OnetoN"))
                                               [(string2ac rName)]]]

--finding second entity belonging to an MtoN relationship                                                
getCorEnt :: [Entity] -> String -> String -> String
getCorEnt [] _ _ = ""  -- this should not happen
getCorEnt ((Entity name attrs):ents) eName rName = 
  if name == rName 
   then checkAttributes attrs eName
   else getCorEnt ents eName rName
  where checkAttributes ((Attribute _ typ _ _):atts) n =
           case typ of
             (KeyDom kName) -> if kName == n 
                                 then checkAttributes atts n
                                 else kName
             _              -> checkAttributes atts n
        checkAttributes [] _ = "" --should not happen
 

-- generates data term providing for each attribute (name) 
-- if it is nullable or not
getNullableAttr :: Entity -> [CExpr] 
getNullableAttr (Entity name attrs) = (map (getNullValue name) attrs) 

getNullValue :: String -> Attribute -> CExpr
getNullValue (e:name) (Attribute aName _ _ nullable) =  
        tupleExpr [string2ac ((toLower e):name ++ aName) 
                   , (CSymbol (pre (show nullable)))]

-- generates data term providing the type of each attribute
getAttrTypes :: Entity -> [CExpr]
getAttrTypes (Entity name attrs) =  
                (map (getTypeOf name) attrs)
                                        
getTypeOf :: String -> Attribute -> CExpr
getTypeOf (e:name) (Attribute aName domain key _) = 
 case domain of
    (IntDom _ ) -> case key of
                     PKey -> tupleExpr [string2ac((toLower e):name 
                                                  ++aName),
                                        string2ac ((toUpper e):name)]
                     NoKey -> tupleExpr [string2ac ((toLower e):name
                                                    ++aName),
                                         string2ac "int"]
                     Unique -> tupleExpr [string2ac ((toLower e):name 
                                                    ++aName),
                                          string2ac "int"]
    (FloatDom _ ) -> tupleExpr [string2ac ((toLower e):name 
                                            ++aName),
                                string2ac "float"]
    (CharDom _ )  -> tupleExpr [string2ac ((toLower e):name
                                            ++aName),
                                string2ac "char"]
    (StringDom _ ) ->  tupleExpr [string2ac ((toLower e):name
                                             ++aName),
                                  string2ac "string"]
    (BoolDom _ )   -> tupleExpr [string2ac ((toLower e):name
                                              ++aName),
                                 string2ac "bool"]
    (DateDom _ ) -> tupleExpr [string2ac ((toLower e):name
                                            ++aName),
                               string2ac "date"]
    (KeyDom e2Name ) -> tupleExpr [string2ac ((toLower e):name
                                               ++aName),
                                   string2ac e2Name]
                             


-- generates data term providing for each tableName the list of its attributes
getAttrList :: Entity -> CExpr
getAttrList (Entity name attrs) =
  tupleExpr [(string2ac (lowerCase name)), 
              tupleExpr [(string2ac name), (list2ac (map selectAttr attrs))]]    
     where selectAttr (Attribute aname _ _ _) = string2ac aname

-- ------- writing file containing all type needed for use of CDBI ------------

-- Generates the declaration of datatype and ID-type for each entity.   
getEntityTypeDecls :: String -> Entity -> [CTypeDecl] 
getEntityTypeDecls mName ent =                        
   [(writeDatatype mName ent), (writeID mName ent)]
                           
-- Generates a entity-datatype based on an entity.
writeDatatype :: String -> Entity -> CTypeDecl
writeDatatype mName (Entity name attrs)  = 
 CType (mName, name) Public [] [(CCons (mName, name) 
                                       Public
                                       (map (writeAttributes mName name) attrs))]
                    
-- Generates a ID-datatype based on an entity.
writeID :: String -> Entity -> CTypeDecl
writeID mName (Entity name _) = 
 CType (mName, (name++"ID")) Public [] [(CCons (mName, (name ++"ID"))
                                               Public
                                               [intType])] 

-- Generates all function declarations for an entity.                                               
getEntityFuncDecls :: String -> Entity -> [CFuncDecl]
getEntityFuncDecls mName ent = 
      [(writeDescription mName ent), 
       (writeTables mName ent)]++
      (writeColumns mName ent)++
      (writeColumnDescriptions mName ent)++
      (writeGetterSetters mName ent)++
      (writeKeyToValueFunc mName ent)

-- Generates an entity-description based on an entity.
writeDescription :: String -> Entity -> CFuncDecl
writeDescription mName (Entity name attrs) = 
  cmtfunc ("The ER description of the `" ++ name ++ "` entity.")
        (mName, (firstLow name ++ "_CDBI_Description" ))
        0
        Public
        (CTCons (mDescription, "EntityDescription") [baseType (mName, name)])
        [(simpleRule [] (applyE (CSymbol (mDescription, "ED"))
                                [(string2ac name),
                                 (list2ac (map writeTypes attrs)),
                                 (writeTransFunOne mName name attrs),
                                 (writeTransFunTwo mName name attrs),
                                 (writeTransFunThree mName name attrs)]))]


-- Generates a table-type based on an entity.
writeTables :: String -> Entity -> CFuncDecl
writeTables mName (Entity name _) = 
  cmtfunc ("The database table of the `" ++ name ++ "` entity.")
        (mName, firstLow name ++ "Table")
        0
        Public
        (CTCons (mDescription, "Table") [])
        [(simpleRule [] (string2ac name))]

-- Generates Column Descriptions based on an entity.        
writeColumnDescriptions :: String -> Entity -> [CFuncDecl]
writeColumnDescriptions mName (Entity name attrs) = 
  map (writeColumnDescription mName name) attrs

writeColumnDescription :: String -> String -> Attribute -> CFuncDecl
writeColumnDescription mName name a@(Attribute atr _ _ _) =
  cmtfunc ("The description of the database column `" ++ atr ++
           "` of the `" ++ name ++ "` entity.")
        (mName, firstLow name ++ atr ++ "ColDesc")
        0
        Public
        (CTCons (mDescription, "ColumnDescription") 
                [(writeAttributes mName name a)])
        [(simpleRule [] (applyE (CSymbol (mDescription, "ColDesc"))
                                [(string2ac ("\"" ++ name ++ "\"." ++ "\"" 
                                              ++ atr ++ "\"")),
                                 (writeTypes a),
                                 (CLambda [(writeAttrLeftOneTwo mName name a)]
                                          (writeAttrRightOneTwo 1 a)),
                                 (CLambda [(writeAttrLeftThree a)]
                                          (writeAttrRightThree mName name a))]))]                                        

-- Generates all needed column-functions based on an entity.
writeColumns :: String -> Entity -> [CFuncDecl]
writeColumns mName (Entity name attrs) =
     map (writeColumn mName name ) attrs

-- Generates a column-function from an attribute.
writeColumn :: String -> String -> Attribute -> CFuncDecl
writeColumn mName name a@(Attribute atr _ _ _) =
    cmtfunc ("The database column `" ++ atr ++
             "` of the `" ++ name ++ "` entity.")
          (mName, firstLow name ++ "Column" ++ atr)
          0
          Public
          (CTCons (mDescription, "Column") [(getAttributeType mName name a)])
          [(simpleRule [] (applyE (CSymbol (mDescription, "Column"))
                                  [(string2ac ("\"" ++ atr ++ "\"")),
                                   (string2ac ("\"" ++ name ++ "\"." 
                                       ++ "\"" ++ atr ++ "\"")) ]))]

getAttributeType :: String -> String -> Attribute -> CTypeExpr
getAttributeType mName eName (Attribute atr dom _ _) =
  if atr == "Key" then baseType (mName, eName ++ "ID")
                  else getType mName dom

-- Get the type of a domain as CExpr.
getType :: String -> Domain -> CTypeExpr
getType _ (IntDom _) = intType
getType _ (FloatDom _) = floatType
getType _ (CharDom _) = (baseType (pre "Char"))
getType _ (StringDom _) = stringType
getType _ (BoolDom _) = boolType
getType _ (DateDom _) = (baseType ("Time", "ClockTime"))
getType mName (KeyDom name) = (baseType (mName ,(name++"ID")))

-- Generates all getter and setter methods based on an entity.
writeGetterSetters :: String -> Entity -> [CFuncDecl]
writeGetterSetters mName (Entity name attrs) = 
 let indAttrs = zip attrs [1..(length attrs)]
  in (map (writeGetter mName name (length attrs)) indAttrs) ++
     (map (writeSetter mName name (length attrs)) indAttrs)

-- Generates a setter method based on an attribute.
writeSetter :: String -> String -> Int -> (Attribute, Int) -> CFuncDecl
writeSetter mName eName len (att@(Attribute name _ _ _), i) = 
  cmtfunc ("Sets the attribute `" ++ name ++
           "` of the `" ++ eName ++ "` entity.")
        (mName, ("set" ++ eName ++ name))
        2
        Public
        ((baseType (mName, eName)) ~> (writeAttributes mName eName att) 
                                    ~> (baseType (mName, eName)))
        [(simpleRule [(CPComb (mName, eName) (createParametersLeft i (len-i))),
                      (cpvar "a")]
                     (applyE (CSymbol (mName, eName))
                             (createParametersRight i (len-i))))]

-- Generates a getter method based on an attribute.
writeGetter :: String -> String -> Int -> (Attribute, Int) -> CFuncDecl
writeGetter mName eName len (att@(Attribute name _ _ _), i) = 
  cmtfunc ("Gets the attribute `" ++ name ++
           "` of the `" ++ eName ++ "` entity.")
        (mName, ((firstLow eName) ++ name))
        1
        Public
        ((baseType (mName, eName)) ~> (writeAttributes mName eName att))
        [(simpleRule [CPComb (mName, eName) (createUnderscores i (len-i))]
                     (cvar "a"))]

-- Auxiliary function for writeGetterSetter that creates the needed
-- amount of underscores and places the "a" at the correct position
createUnderscores :: Int -> Int -> [CPattern]
createUnderscores ind len = case ind of
  0 -> case len of
         0 -> []
         n -> (cpvar "_") : (createUnderscores 0 $ n-1)
  1 -> (cpvar "a") : (createUnderscores 0 len)
  n -> (cpvar "_") : (createUnderscores (n-1) len)

-- Auxiliary function for writeGetterSetter that creates the needed
-- amount of parameters for setter-functions on the left side
createParametersLeft :: Int -> Int -> [CPattern]
createParametersLeft ind len = case ind of
  0 -> case len of
         0 -> []
         n -> (cpvar ("b" ++ (show n))):(createParametersLeft 0 $ n-1)
  1 -> (cpvar "_"): (createParametersLeft 0 len)
  n -> (cpvar ("a" ++ (show n))) : (createParametersLeft (n-1) len)

-- Auxiliary function for writeGetterSetter that creates the needed amount
-- of parameters for setter-functions on the right side
createParametersRight :: Int -> Int -> [CExpr]
createParametersRight ind len = case ind of
  0 -> case len of
         0 -> []
         n -> (cvar ("b" ++ (show n))) : (createParametersRight 0 $ n-1)
  1 -> (cvar ("a")) : (createParametersRight 0 len)
  n -> (cvar ("a" ++ (show n))) : (createParametersRight (n-1) len)

-- Generates the first conversion function in the entity-description
writeTransFunOne :: String -> String -> [Attribute] -> CExpr
writeTransFunOne mName name attrs = 
  CLambda [(CPComb (mName, name) 
                  (map (writeAttrLeftOneTwo mName name) attrs))]
          (list2ac (map (writeAttrRightOneTwo 1) attrs))

-- Generates the second conversion function in the entity-description
writeTransFunTwo :: String -> String -> [Attribute] -> CExpr
writeTransFunTwo mName name attrs =
  CLambda [(CPComb (mName, name)
                  (map (writeAttrLeftOneTwo mName name) attrs))]
          (list2ac (map (writeAttrRightOneTwo 2 ) attrs))

-- Generates the third conversion function in the entity-description
writeTransFunThree :: String -> String -> [Attribute] -> CExpr
writeTransFunThree mName name attrs =
  CLambda [(listPattern (map writeAttrLeftThree attrs))] 
          (applyE (CSymbol (mName, name)) 
                  (map (writeAttrRightThree mName name) attrs))

--Generates left-hand-side of first and second conversion function.
writeAttrLeftOneTwo :: String -> String -> Attribute -> CPattern
writeAttrLeftOneTwo mName _ (Attribute (a:b) dom NoKey _) =
  case dom of
    KeyDom c -> (CPComb (mName, (c++"ID")) [cpvar ((toLower a):b)])
    _        -> cpvar ((toLower a):b)
writeAttrLeftOneTwo mName _ (Attribute (a:b) dom Unique _) =
  case dom of
    KeyDom c -> (CPComb (mName, (c++"ID")) [cpvar ((toLower a):b)])
    _        -> cpvar ((toLower a):b) 
writeAttrLeftOneTwo mName  _  (Attribute (a:b) (KeyDom c) PKey _) =
    (CPComb (mName, (c++"ID")) [cpvar ((toLower a):b)])
writeAttrLeftOneTwo mName name (Attribute (a:b) (IntDom _) PKey _) =
    (CPComb (mName, (name++"ID")) [cpvar ((toLower a):b)])         
                  
--Generates right-hand-side of first and second conversion function.
writeAttrRightOneTwo :: Int -> Attribute -> CExpr
writeAttrRightOneTwo 1 (Attribute (a:b) (IntDom _) _ False) =
 applyE (CSymbol (mConnection, "SQLInt")) [cvar ((toLower a):b)]
writeAttrRightOneTwo 2 (Attribute name@(a:b) (IntDom _) _ False) =
  if name == "Key" 
   then (constF (mConnection, "SQLNull"))
   else (applyE (CSymbol (mConnection, "SQLInt")) [cvar ((toLower a):b)])
writeAttrRightOneTwo _ (Attribute (a:b) (IntDom _) _ True) =
  applyF (mDescription, "sqlIntOrNull") [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (FloatDom _) _ False) =
  applyE (CSymbol (mConnection, "SQLFloat")) [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (FloatDom _) _ True) =
  applyF (mDescription, "sqlFloatOrNull") [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (CharDom _) _ False) =
  applyE (CSymbol (mConnection, "SQLChar")) [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (CharDom _) _ True) =
  applyF (mDescription, "sqlCharOrNull") [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (StringDom _) _ False) =
  applyE (CSymbol (mConnection, "SQLString")) [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (StringDom _) _ True) =
  applyF (mDescription, "sqlString") [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (BoolDom _) _ False) =
  applyE (CSymbol (mConnection, "SQLBool")) [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (BoolDom _) _ True) =
  applyF (mDescription, "sqlBoolOrNull") [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (DateDom _) _ False) =
  applyE (CSymbol (mConnection, "SQLDate")) [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (DateDom _) _ True) =
  applyF (mDescription, "sqlDateOrNull") [cvar ((toLower a):b)]
writeAttrRightOneTwo _ (Attribute (a:b) (KeyDom _) _ False) =
  applyE (CSymbol (mConnection, "SQLInt")) [cvar ((toLower a):b)]

--Generates left-hand-side of third conversion function.
writeAttrLeftThree :: Attribute -> CPattern
writeAttrLeftThree (Attribute (a:b) (IntDom _) _ False) =
    CPComb (mConnection, "SQLInt") [cpvar ((toLower a):b)]  
writeAttrLeftThree (Attribute (a:b) (FloatDom _) _ False) =
    CPComb (mConnection, "SQLFloat") [cpvar ((toLower a):b)]
writeAttrLeftThree (Attribute (a:b) (CharDom _) _ False) =
    CPComb (mConnection, "SQLChar") [cpvar ((toLower a):b)] 
writeAttrLeftThree (Attribute (a:b) (StringDom _) _ False) =
    CPComb (mConnection, "SQLString") [cpvar ((toLower a):b)]  
writeAttrLeftThree (Attribute (a:b) (BoolDom _) _ False) =
    CPComb (mConnection, "SQLBool") [cpvar ((toLower a):b)]  
writeAttrLeftThree (Attribute (a:b) (DateDom _) _ False) =
    CPComb (mConnection, "SQLDate") [cpvar ((toLower a):b)] 
writeAttrLeftThree (Attribute (a:b) (KeyDom _) _ False) =
    CPComb (mConnection, "SQLInt") [cpvar ((toLower a):b)] 
writeAttrLeftThree (Attribute (a:b) _ _ True) =
    cpvar ((toLower a):b)       

--Generates right-hand-side of third conversion function
writeAttrRightThree ::String -> String -> Attribute -> CExpr
writeAttrRightThree _ _ (Attribute (a:b) (IntDom _) NoKey True) =
  applyF (mDescription, "intOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (FloatDom _) NoKey True) =
  applyF (mDescription, "floatOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (CharDom _) NoKey True) =
  applyF (mDescription, "charOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (StringDom _) NoKey True) =
  applyF (mDescription, "fromStringOrNull") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (BoolDom _) NoKey True) =
  applyF (mDescription, "boolOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (DateDom _) NoKey True) =
  applyF (mDescription, "dateOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree mName _ (Attribute (a:b) (KeyDom c) NoKey True) =
  applyE (CSymbol (mName, (c++"ID"))) [(applyF (mDescription, "intOrNothing")
                                               [cvar ((toLower a):b)])] 
writeAttrRightThree _ _ (Attribute (a:b) (IntDom _) Unique True) =
  applyF (mDescription, "intOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (FloatDom _) Unique True) =
  applyF (mDescription, "floatOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (CharDom _) Unique True) =
  applyF (mDescription, "charOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (StringDom _) Unique True) =
  applyF (mDescription, "fromStringOrNull") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (BoolDom _) Unique True) =
  applyF (mDescription, "boolOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree _ _ (Attribute (a:b) (DateDom _) Unique True) =
  applyF (mDescription, "dateOrNothing") [cvar ((toLower a):b)]
writeAttrRightThree mName _ (Attribute (a:b) (KeyDom c) Unique True) =
  applyE (CSymbol (mName, (c++"ID"))) [(applyF (mDescription, "intOrNothing")
                                              [cvar ((toLower a):b)])] 
writeAttrRightThree mName _ (Attribute (a:b) dom NoKey False) = 
  case dom of
     (KeyDom d) -> applyE (CSymbol (mName, (d++"ID"))) [(cvar ((toLower a):b))]
     _          -> cvar ((toLower a):b)
writeAttrRightThree mName _ (Attribute (a:b) dom Unique False) =
  case dom of
     (KeyDom d) -> applyE (CSymbol (mName, (d++"ID"))) [(cvar ((toLower a):b))]
     _          -> cvar ((toLower a):b)
writeAttrRightThree mName _ (Attribute (a:b) (KeyDom c) PKey _) =
  applyE (CSymbol (mName, (c++"ID"))) [(cvar ((toLower a):b))]  
writeAttrRightThree mName name (Attribute (a:b) (IntDom _) PKey _) =
  applyE (CSymbol (mName, (name++"ID"))) [(cvar ((toLower a):b))]  

-- Generates the attribute types to create an entity-datatype.
writeAttributes :: String -> String -> Attribute -> CTypeExpr
writeAttributes _ _ (Attribute _ (IntDom _) _ True) = maybeType intType
writeAttributes mName name (Attribute a (IntDom _) _ False) = 
   case a of
     "Key" -> baseType (mName , (name++"ID"))
     _     -> intType
writeAttributes _ _ (Attribute _ (FloatDom _) _ null) =
  addMaybeIfNull null floatType
writeAttributes _ _ (Attribute _ (CharDom _) _ null) = 
  addMaybeIfNull null (baseType (pre "Char"))
writeAttributes _ _ (Attribute _ (StringDom _) _ _) = stringType
writeAttributes _ _ (Attribute _ (BoolDom _) _ n) = addMaybeIfNull n boolType
writeAttributes _ _ (Attribute _ (DateDom _) _ null) = 
  addMaybeIfNull null (baseType ("Time", "ClockTime"))
writeAttributes mName _ (Attribute _ (KeyDom k) _ null) = 
  addMaybeIfNull null (baseType (mName ,(k++"ID")))

addMaybeIfNull :: Bool -> CTypeExpr -> CTypeExpr
addMaybeIfNull isnull texp = if isnull then maybeType texp else texp

-- Generates attribute types to create an entity-description.
writeTypes :: Attribute -> CExpr
writeTypes (Attribute _ (IntDom _) _ _) = CSymbol (mConnection, "SQLTypeInt")
writeTypes (Attribute _ (FloatDom _) _ _) = CSymbol (mConnection, "SQLTypeFloat")
writeTypes (Attribute _ (CharDom _) _ _) = CSymbol (mConnection, "SQLTypeChar")
writeTypes (Attribute _ (StringDom _) _ _) = CSymbol (mConnection, "SQLTypeString")
writeTypes (Attribute _ (BoolDom _) _ _) = CSymbol (mConnection, "SQLTypeBool")
writeTypes (Attribute _ (DateDom _) _ _) = CSymbol (mConnection, "SQLTypeDate")
writeTypes (Attribute _ (KeyDom _) _ _) = CSymbol (mConnection, "SQLTypeInt")

--Generates id-to-Value function based on an entity.
writeKeyToValueFunc :: String -> Entity -> [CFuncDecl]
writeKeyToValueFunc mName (Entity name attrs) =
  case (head attrs) of
     (Attribute "Key" _ PKey _ ) -> 
           [cfunc (mName , ((firstLow name) ++ "ID"))
                  1
                  Public
                  ((baseType (mName, ((name ++"ID")))) ~> 
                       (CTCons ("Database.CDBI.Criteria", "Value") 
                               [(baseType (mName, (name++"ID")))]))
                  [(simpleRule [(writeAttrLeftOneTwo mName name (head attrs))]
                               (applyF ("Database.CDBI.Criteria", "idVal") 
                                       [(cvar "key")]))]]
     _  -> []

-- Creates a sqlite3-database (sqlite3 needs to be installed)
createDatabase :: [Entity] -> Handle -> IO ()
createDatabase ents db = mapIO_ (\ent -> (createDatabase' ent)) ents
 where
  createDatabase' (Entity name (a:atr)) =
    case a of
      (Attribute "Key" _ _ _) -> do
        hPutStrLn db ("create table '" ++ name ++ "'(" ++
                      (foldl (\y x -> y ++ " ," ++ (writeDBAttributes x))
                             (writeDBAttributes a)
                             atr) ++ ");")
      _ -> do let str = ("create table '" ++ name ++ "'(" ++
                         (foldl (\y x -> y ++ " ," ++ (writeDBRelationship x))
                                (writeDBRelationship a)
                                atr) ++
                         ", primary key (" ++
                         (writePrimaryKey (a:atr)) ++ "));")
              hPutStrLn db str

-- Write Attribute for table-creation (Used when first Attribute
-- of Entity is named "Key" because the primary key will be that "Key" then)
writeDBAttributes :: Attribute -> String
writeDBAttributes (Attribute name ty key nullable) =
    "'" ++ name ++ "'" ++
            (case ty of
                 IntDom Nothing      -> ""
                 IntDom _      -> " int"
                 FloatDom _    -> " float"
                 CharDom _     -> " char"
                 StringDom _   -> " string"
                 BoolDom _     -> " boolean"
                 DateDom _     -> " string"
                 KeyDom str    -> " int " ++ "REFERENCES '" ++ str ++ "'(Key)") ++
            (case key of
                 PKey   -> " integer primary key"
                 Unique -> " unique"
                 NoKey  -> "") ++
            (case nullable of
                 True  -> ""
                 False -> if key == PKey then ""
                                         else " not null")

-- Same as writeDBAttributes but for the case that the first Attribute of
-- Entity is not named "Key", because there will be a combined primary key then
-- and the string needs to be built a little different then
writeDBRelationship :: Attribute -> String
writeDBRelationship (Attribute name ty key nullable) =
  "'" ++  name ++ "'" ++
            (case ty of
                 IntDom _    -> " int"
                 FloatDom _  -> " float "
                 CharDom _   -> " char "
                 StringDom _ -> " string "
                 BoolDom _   -> " boolean "
                 DateDom _   -> " string "
                 KeyDom str    -> " int " ++ "REFERENCES '" ++ str ++"'(Key)")
         ++ (case key of
                 Unique -> " unique"
                 _  -> "")
         ++ (case nullable of
                 True  -> ""
                 False -> " not null")

-- Write a combined primary key
writePrimaryKey :: [Attribute] -> String
writePrimaryKey ((Attribute name _ PKey _):atr) =
  "'" ++ name ++ "'" ++
  (case (writePrimaryKey atr) of
     "" -> ""
     x  -> ", " ++ x)
writePrimaryKey ((Attribute _ _ Unique _):atr) = writePrimaryKey atr
writePrimaryKey ((Attribute _ _ NoKey _):atr) = writePrimaryKey atr
writePrimaryKey [] = ""

   
firstLow :: String -> String
firstLow [] = []
firstLow (s:str) = (toLower s):str

lowerCase :: String -> String
lowerCase str = map toLower str

spaceN :: Int -> String
spaceN n | n == 0 = ""
         | otherwise = ' ':(spaceN (n-1))
