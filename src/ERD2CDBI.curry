------------------------------------------------------------------------------
--- This module creates all datatypes to represent the entities and
--- relations of a relational (SQLite) database corresponding to a
--- logical ER model specified in a file `x_ERDT.term` (which is
--- a transformed ER-Model that was translated by erd2curry).
--- It produces a Curry program `x_CDBI.curry` and a file
--- `x_SQLCODE.info` that is used when embedded SQL statements are
--- translated by the Curry preprocessor `currypp`.
---
--- @author Mike Tallarek, extensions by Julia Krone and Michael Hanus
------------------------------------------------------------------------------
--- TODO: generate code to check ER constraints in new/update/delete
---       operations for entities (similarly to old erd2curry compiler)

{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

import Char           ( toLower, toUpper )
import Directory      ( doesFileExist, getAbsolutePath )
import Distribution   ( installDir )
import qualified FilePath as FP ( (</>), combine, splitFileName)
import IO
import IOExts         ( connectToCommand )
import List
import ReadShowTerm   ( readsQTerm )
import System
import Time

import AbstractCurry.Types
import AbstractCurry.Pretty
import AbstractCurry.Build
import Database.ERD
import Database.ERD.Goodies
import Control.SetFunctions ( selectValue, set2 )
import Text.Pretty

-- Write all the data so CDBI can be used, create a database (if it does
-- not exist) and a `.info` file.
-- The parameters are the name of the file containing the ERD term,
-- the ER model, and the name of the SQLite3 database.
writeCDBI :: String -> ERD -> String -> IO ()
writeCDBI erdfname (ERD name ents rels) dbname = do
  dbPath <- getAbsolutePath dbname
  let cdbimod  = name
      cdbiFile = cdbimod++".curry"
      imports  = [ "Time"
                 , "Database.CDBI.ER"
                 , "Database.CDBI.Criteria"
                 , "Database.CDBI.Connection"
                 , "Database.CDBI.Description"]
      typeDecls  = foldr ((++) . (genEntityTypeDecls cdbimod)) [] ents 
      funcDecls  = genDBPathFunc cdbimod dbPath :
                   foldr ((++) . (genEntityFuncDecls cdbimod)) [] ents ++
                   genNewDBSchema cdbimod ents ++
                   genSaveDB cdbimod ents ++
                   genRunFuncs cdbimod
  writeFile cdbiFile $ unlines $
    map ("--- "++)
        [ "This file has been generated from"
        , ""
        , "    " ++ erdfname
        , ""
        , "and contains definitions for all entities and relations"
        , "specified in this model.\n"] ++
    [ pPrint
       (ppCurryProg defaultOptions
         (CurryProg cdbimod imports Nothing [] [] typeDecls funcDecls [])) ]
  putStrLn $ "Database operations generated into file '" ++ cdbiFile ++ "'"
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
    hPutStrLn db $ unlines (map entity2createTable ents)
    hClose db

genDBPathFunc :: String -> String -> CFuncDecl
genDBPathFunc mname dbPath =
  stCmtFunc "The name of the SQLite database file."
          (mname,"sqliteDBFile")
          0 Public stringType [simpleRule [] (string2ac dbPath)]

-- -----writing .info-file containing auxiliary data for parsing -------------

-- Auxiliary definitions for qualified names in AbstractCurry
mDescr :: String
mDescr = "Database.CDBI.Description"

mConn :: String
mConn = "Database.CDBI.Connection"

mER :: String
mER = "Database.CDBI.ER"

-- generates an AbstractCurry expression representing the parser information
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
                                      string2ac name,
                                      relations, 
                                      nullables,
                                      attributes,
                                      attrTypes])))  
    where relations = list2ac (foldr ((++) . getRelationTypes ents) [] rels)
          nullables = list2ac (foldr ((++) . getNullableAttr) [] ents) 
          attributes = list2ac (map getAttrList ents)
          attrTypes = list2ac (foldr ((++) . getAttrTypes) [] ents) 


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
getNullValue ename (Attribute aName _ _ nullable) =  
        tupleExpr [string2ac (firstLow ename ++ aName) 
                  , CSymbol (pre (show nullable))]

-- generates data term providing the type of each attribute
getAttrTypes :: Entity -> [CExpr]
getAttrTypes (Entity name attrs) =  
                (map (getTypeOf name) attrs)
                                        
getTypeOf :: String -> Attribute -> CExpr
getTypeOf ename (Attribute aName domain key _) = 
 case domain of
    (IntDom _ ) -> case key of
                     PKey -> tupleExpr [string2ac (firstLow ename ++ aName),
                                        string2ac (firstUp ename)]
                     NoKey -> tupleExpr [string2ac (firstLow ename ++ aName),
                                         string2ac "int"]
                     Unique -> tupleExpr [string2ac (firstLow ename ++ aName),
                                          string2ac "int"]
    (FloatDom _ ) -> tupleExpr [string2ac (firstLow ename ++ aName),
                                string2ac "float"]
    (CharDom _ )  -> tupleExpr [string2ac (firstLow ename ++ aName),
                                string2ac "char"]
    (StringDom _ ) ->  tupleExpr [string2ac (firstLow ename ++ aName),
                                  string2ac "string"]
    (BoolDom _ )   -> tupleExpr [string2ac (firstLow ename ++ aName),
                                 string2ac "bool"]
    (DateDom _ ) -> tupleExpr [string2ac (firstLow ename ++ aName),
                               string2ac "date"]
    (KeyDom e2Name ) -> tupleExpr [string2ac (firstLow ename ++ aName),
                                   string2ac e2Name]


-- Generates data term providing for each tableName the list of its attributes
getAttrList :: Entity -> CExpr
getAttrList (Entity name attrs) =
  tupleExpr [string2ac (lowerCase name),
             tupleExpr [(string2ac name),
             list2ac (map (string2ac . attributeName) attrs)]]    

------------------------------------------------------------------------------
-- Generating Curry program containing all type/operations needed for CDBI use

-- Generates the declaration of datatype and ID-type for each entity.   
genEntityTypeDecls :: String -> Entity -> [CTypeDecl] 
genEntityTypeDecls mName ent =                        
   [genEntityType mName ent, genIDType mName ent]
                           
-- Generates a entity-datatype based on an entity.
genEntityType :: String -> Entity -> CTypeDecl
genEntityType mName (Entity name attrs)  = 
 CType (mName, name) Public []
       [simpleCCons (mName, name) Public
                    (map (attr2CType mName name) attrs)]
       [pre "Eq", pre "Show", pre "Read"]
                    
-- Generates a ID-datatype based on an entity.
genIDType :: String -> Entity -> CTypeDecl
genIDType mName (Entity name _) = 
 CType (mName, (name++"ID")) Public []
       [simpleCCons (mName, (name ++"ID")) Public [intType]]
       [pre "Eq", pre "Show", pre "Read"]

-- Generates all function declarations for an entity.                                               
genEntityFuncDecls :: String -> Entity -> [CFuncDecl]
genEntityFuncDecls mName ent =
      [genEntityDescription mName ent, genTables mName ent] ++
      genColumns mName ent ++
      genColumnDescriptions mName ent ++
      genGetterSetters mName ent ++
      genKeyTransformFuncs mName ent ++
      genEntryFuncs mName ent

-- Generates an entity-description based on an entity.
genEntityDescription :: String -> Entity -> CFuncDecl
genEntityDescription mName (Entity name attrs) = 
  stCmtFunc ("The ER description of the `" ++ name ++ "` entity.")
        (mName, firstLow name ++ "_CDBI_Description" )
        0
        Public
        (applyTC (mDescr, "EntityDescription") [baseType (mName, name)])
        [(simpleRule [] (applyE (CSymbol (mDescr, "ED"))
                                [string2ac name,
                                 list2ac (map attr2CSymbol attrs),
                                 writeTransFunOne mName name attrs,
                                 writeTransFunTwo mName name attrs,
                                 writeTransFunThree mName name attrs]))]


-- Generates a table description for on an entity.
genTables :: String -> Entity -> CFuncDecl
genTables mName (Entity name _) = 
  stCmtFunc ("The database table of the `" ++ name ++ "` entity.")
        (mName, firstLow name ++ "Table")
        0
        Public
        (baseType (mDescr, "Table"))
        [(simpleRule [] (string2ac name))]

-- Generates Column Descriptions based on an entity.        
genColumnDescriptions :: String -> Entity -> [CFuncDecl]
genColumnDescriptions mName (Entity name attrs) = 
  map (genColumnDescription mName name) attrs

genColumnDescription :: String -> String -> Attribute -> CFuncDecl
genColumnDescription mName name a@(Attribute atr _ _ _) =
  stCmtFunc ("The description of the database column `" ++ atr ++
             "` of the `" ++ name ++ "` entity.")
    (mName, firstLow name ++ atr ++ "ColDesc")
    0
    Public
    (applyTC (mDescr, "ColumnDescription")  [(attr2CType mName name a)])
    [simpleRule []
       (applyE (CSymbol (mDescr, "ColDesc"))
               [string2ac ("\"" ++ name ++ "\"." ++ "\"" ++ atr ++ "\""),
                attr2CSymbol a,
                CLambda [genAttrConvLeftOneTwo mName name a]
                        (genAttrConvRightOneTwo mName False a),
                CLambda [genAttrConvLeftThree a]
                        (genAttrConvRightThree mName name a)])]

-- Generates all needed column-functions based on an entity.
genColumns :: String -> Entity -> [CFuncDecl]
genColumns mName (Entity name attrs) =
     map (genColumn mName name ) attrs

-- Generates a column-function from an attribute.
genColumn :: String -> String -> Attribute -> CFuncDecl
genColumn mName name a@(Attribute atr _ _ _) =
    stCmtFunc ("The database column `" ++ atr ++
             "` of the `" ++ name ++ "` entity.")
          (mName, firstLow name ++ "Column" ++ atr)
          0
          Public
          (applyTC (mDescr, "Column") [(getAttributeType mName name a)])
          [(simpleRule [] (applyE (CSymbol (mDescr, "Column"))
                                  [(string2ac ("\"" ++ atr ++ "\"")),
                                   (string2ac ("\"" ++ name ++ "\"." 
                                       ++ "\"" ++ atr ++ "\"")) ]))]

getAttributeType :: String -> String -> Attribute -> CTypeExpr
getAttributeType mName eName (Attribute atr dom _ _) =
  if atr == "Key" then baseType (mName, eName ++ "ID")
                  else getType mName dom

-- Get the type of a domain as CExpr.
getType :: String -> Domain -> CTypeExpr
getType _ (IntDom _)        = intType
getType _ (FloatDom _)      = floatType
getType _ (CharDom _)       = baseType (pre "Char")
getType _ (StringDom _)     = stringType
getType _ (BoolDom _)       = boolType
getType _ (DateDom _)       = baseType ("Time", "ClockTime")
getType mName (KeyDom name) = baseType (mName, name++"ID")

-- Generates all getter and setter methods based on an entity.
genGetterSetters :: String -> Entity -> [CFuncDecl]
genGetterSetters mName (Entity name attrs) = 
 let indAttrs = zip attrs [1..(length attrs)]
  in map (genGetter mName name (length attrs)) indAttrs ++
     map (genSetter mName name (length attrs)) indAttrs

-- Generates a setter method based on an attribute.
genSetter :: String -> String -> Int -> (Attribute, Int) -> CFuncDecl
genSetter mName eName len (att@(Attribute name _ _ _), i) = 
  stCmtFunc ("Sets the attribute `" ++ name ++
           "` of the `" ++ eName ++ "` entity.")
        (mName, ("set" ++ eName ++ name))
        2
        Public
        ((baseType (mName, eName)) ~> (attr2CType mName eName att) 
                                    ~> (baseType (mName, eName)))
        [(simpleRule [(CPComb (mName, eName) (createParametersLeft i (len-i))),
                      (cpvar "a")]
                     (applyE (CSymbol (mName, eName))
                             (createParametersRight i (len-i))))]

-- Generates a getter method based on an attribute.
genGetter :: String -> String -> Int -> (Attribute, Int) -> CFuncDecl
genGetter mName eName len (att@(Attribute name _ _ _), i) = 
  stCmtFunc ("Gets the attribute `" ++ name ++
           "` of the `" ++ eName ++ "` entity.")
        (mName, ((firstLow eName) ++ name))
        1
        Public
        ((baseType (mName, eName)) ~> (attr2CType mName eName att))
        [(simpleRule [CPComb (mName, eName) (createUnderscores i (len-i))]
                     (cvar "a"))]

-- Auxiliary function for genGetterSetter that creates the needed
-- amount of underscores and places the "a" at the correct position
createUnderscores :: Int -> Int -> [CPattern]
createUnderscores ind len = case ind of
  0 -> case len of
         0 -> []
         n -> (cpvar "_") : (createUnderscores 0 $ n-1)
  1 -> (cpvar "a") : (createUnderscores 0 len)
  n -> (cpvar "_") : (createUnderscores (n-1) len)

-- Auxiliary function for genGetterSetter that creates the needed
-- amount of parameters for setter-functions on the left side
createParametersLeft :: Int -> Int -> [CPattern]
createParametersLeft ind len = case ind of
  0 -> case len of
         0 -> []
         n -> (cpvar ("b" ++ show n)):(createParametersLeft 0 $ n-1)
  1 -> (cpvar "_"): (createParametersLeft 0 len)
  n -> (cpvar ("a" ++ show n)) : (createParametersLeft (n-1) len)

-- Auxiliary function for genGetterSetter that creates the needed amount
-- of parameters for setter-functions on the right side
createParametersRight :: Int -> Int -> [CExpr]
createParametersRight ind len = case ind of
  0 -> case len of
         0 -> []
         n -> (cvar ("b" ++ show n)) : (createParametersRight 0 $ n-1)
  1 -> (cvar "a") : (createParametersRight 0 len)
  n -> (cvar ("a" ++ (show n))) : (createParametersRight (n-1) len)

-- Generates the first conversion function in the entity-description
writeTransFunOne :: String -> String -> [Attribute] -> CExpr
writeTransFunOne mName name attrs =
  CLambda [(CPComb (mName, name) 
                   (map (genAttrConvLeftOneTwo mName name) attrs))]
          (list2ac (map (genAttrConvRightOneTwo mName False) attrs))

-- Generates the second conversion function in the entity-description
-- where the entity key is not used but mapped to a null value.
writeTransFunTwo :: String -> String -> [Attribute] -> CExpr
writeTransFunTwo mName name attrs =
  CLambda [(CPComb (mName, name)
                   (if isPrimaryKeyAttribute (head attrs)
                      then cpvar "_" :
                           map (genAttrConvLeftOneTwo mName name) (tail attrs)
                      else map (genAttrConvLeftOneTwo mName name) attrs))]
          (list2ac (map (genAttrConvRightOneTwo mName True) attrs))

isPrimaryKeyAttribute :: Attribute -> Bool
isPrimaryKeyAttribute (Attribute aname adom _ anull) =
  case adom of
    IntDom _ -> aname == "Key" && not anull
    _        -> False

-- Generates the third conversion function in the entity-description
writeTransFunThree :: String -> String -> [Attribute] -> CExpr
writeTransFunThree mName name attrs =
  CLambda [(listPattern (map genAttrConvLeftThree attrs))] 
          (applyE (CSymbol (mName, name)) 
                  (map (genAttrConvRightThree mName name) attrs))

-- Generates left-hand-side of first and second conversion function.
genAttrConvLeftOneTwo :: String -> String -> Attribute -> CPattern
genAttrConvLeftOneTwo mName _ (Attribute aname dom NoKey isnull) =
  case dom of
    KeyDom c -> if isnull then cpvar (firstLow aname)
                          else CPComb (mName, c++"ID") [cpvar (firstLow aname)]
    _        -> cpvar (firstLow aname)
genAttrConvLeftOneTwo mName _ (Attribute aname dom Unique isnull) =
  case dom of
    KeyDom c -> if isnull then cpvar (firstLow aname)
                          else CPComb (mName, c++"ID") [cpvar (firstLow aname)]
    _        -> cpvar (firstLow aname) 
genAttrConvLeftOneTwo mName  _  (Attribute aname (KeyDom c) PKey _) =
    (CPComb (mName, c++"ID") [cpvar (firstLow aname)])
genAttrConvLeftOneTwo mName name (Attribute aname (IntDom _) PKey _) =
    (CPComb (mName, name++"ID") [cpvar (firstLow aname)])         

-- Generates right-hand-side of first and second conversion function.
-- If second argument is true, a Key attribute is translated into null value.
genAttrConvRightOneTwo :: String -> Bool -> Attribute -> CExpr
genAttrConvRightOneTwo _ False (Attribute aname (IntDom _) _ False) =
 applyE (CSymbol (mConn, "SQLInt")) [cvar (firstLow aname)]
genAttrConvRightOneTwo _ True (Attribute aname (IntDom _) _ False) =
  if aname == "Key" 
   then constF (mConn, "SQLNull")
   else applyE (CSymbol (mConn, "SQLInt")) [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (IntDom _) _ True) =
  applyF (mDescr, "sqlIntOrNull") [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (FloatDom _) _ False) =
  applyE (CSymbol (mConn, "SQLFloat")) [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (FloatDom _) _ True) =
  applyF (mDescr, "sqlFloatOrNull") [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (CharDom _) _ False) =
  applyE (CSymbol (mConn, "SQLChar")) [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (CharDom _) _ True) =
  applyF (mDescr, "sqlCharOrNull") [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (StringDom _) _ False) =
  applyE (CSymbol (mConn, "SQLString")) [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (StringDom _) _ True) =
  applyF (mDescr, "sqlString") [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (BoolDom _) _ False) =
  applyE (CSymbol (mConn, "SQLBool")) [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (BoolDom _) _ True) =
  applyF (mDescr, "sqlBoolOrNull") [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (DateDom _) _ False) =
  applyE (CSymbol (mConn, "SQLDate")) [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (DateDom _) _ True) =
  applyF (mDescr, "sqlDateOrNull") [cvar (firstLow aname)]
genAttrConvRightOneTwo _ _ (Attribute aname (KeyDom _) _ False) =
  applyE (CSymbol (mConn, "SQLInt")) [cvar (firstLow aname)]
genAttrConvRightOneTwo mName _ (Attribute aname (KeyDom c) _ True) =
  applyF (mDescr, "sqlKeyOrNull") [lambdakey2int, cvar (firstLow aname)]
 where
  lambdakey2int = CLambda [CPComb (mName, c++"ID") [cpvar "k"]] (cvar "k")

-- Generates left-hand-side of third conversion function.
genAttrConvLeftThree :: Attribute -> CPattern
genAttrConvLeftThree (Attribute aname (IntDom _) _ False) =
    CPComb (mConn, "SQLInt") [cpvar (firstLow aname)]  
genAttrConvLeftThree (Attribute aname (FloatDom _) _ False) =
    CPComb (mConn, "SQLFloat") [cpvar (firstLow aname)]
genAttrConvLeftThree (Attribute aname (CharDom _) _ False) =
    CPComb (mConn, "SQLChar") [cpvar (firstLow aname)] 
genAttrConvLeftThree (Attribute aname (StringDom _) _ False) =
    CPComb (mConn, "SQLString") [cpvar (firstLow aname)]  
genAttrConvLeftThree (Attribute aname (BoolDom _) _ False) =
    CPComb (mConn, "SQLBool") [cpvar (firstLow aname)]  
genAttrConvLeftThree (Attribute aname (DateDom _) _ False) =
    CPComb (mConn, "SQLDate") [cpvar (firstLow aname)] 
genAttrConvLeftThree (Attribute aname (KeyDom _) _ False) =
    CPComb (mConn, "SQLInt") [cpvar (firstLow aname)] 
genAttrConvLeftThree (Attribute aname _ _ True) =
    cpvar (firstLow aname)       

-- Generates right-hand-side of third conversion function
genAttrConvRightThree ::String -> String -> Attribute -> CExpr
genAttrConvRightThree _ _ (Attribute aname (IntDom _) NoKey True) =
  applyF (mDescr, "intOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (FloatDom _) NoKey True) =
  applyF (mDescr, "floatOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (CharDom _) NoKey True) =
  applyF (mDescr, "charOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (StringDom _) NoKey True) =
  applyF (mDescr, "fromStringOrNull") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (BoolDom _) NoKey True) =
  applyF (mDescr, "boolOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (DateDom _) NoKey True) =
  applyF (mDescr, "dateOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree mName _ (Attribute aname (KeyDom c) NoKey True) =
  applyF (mDescr, "keyOrNothing")
         [CSymbol (mName, c++"ID"), cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (IntDom _) Unique True) =
  applyF (mDescr, "intOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (FloatDom _) Unique True) =
  applyF (mDescr, "floatOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (CharDom _) Unique True) =
  applyF (mDescr, "charOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (StringDom _) Unique True) =
  applyF (mDescr, "fromStringOrNull") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (BoolDom _) Unique True) =
  applyF (mDescr, "boolOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree _ _ (Attribute aname (DateDom _) Unique True) =
  applyF (mDescr, "dateOrNothing") [cvar (firstLow aname)]
genAttrConvRightThree mName _ (Attribute aname (KeyDom c) Unique True) =
  applyF (mDescr, "keyOrNothing")
         [CSymbol (mName, c++"ID"), cvar (firstLow aname)]
genAttrConvRightThree mName _ (Attribute aname dom NoKey False) = 
  case dom of
     (KeyDom d) -> applyE (CSymbol (mName, (d++"ID"))) [(cvar (firstLow aname))]
     _          -> cvar (firstLow aname)
genAttrConvRightThree mName _ (Attribute aname dom Unique False) =
  case dom of
     (KeyDom d) -> applyE (CSymbol (mName, (d++"ID"))) [(cvar (firstLow aname))]
     _          -> cvar (firstLow aname)
genAttrConvRightThree mName _ (Attribute aname (KeyDom c) PKey _) =
  applyE (CSymbol (mName, (c++"ID"))) [(cvar (firstLow aname))]  
genAttrConvRightThree mName name (Attribute aname (IntDom _) PKey _) =
  applyE (CSymbol (mName, (name++"ID"))) [(cvar (firstLow aname))]  

-- Translates an attribute into the corresponding type of entity datatype.
attr2CType :: String -> String -> Attribute -> CTypeExpr
attr2CType mName name (Attribute a adom _ anull) = case adom of
  IntDom _    -> case a of
                   "Key" -> baseType (mName , (name++"ID"))
                   _     -> addMaybeIfNull anull intType
  FloatDom  _ -> addMaybeIfNull anull floatType
  CharDom   _ -> addMaybeIfNull anull (baseType (pre "Char"))
  StringDom _ -> stringType
  BoolDom   _ -> addMaybeIfNull anull boolType
  DateDom   _ -> addMaybeIfNull anull (baseType ("Time", "ClockTime"))
  KeyDom    k -> addMaybeIfNull anull (baseType (mName ,(k++"ID")))
 where
  addMaybeIfNull isnull texp = if isnull then maybeType texp else texp

-- Translates an attribute into the corresponding type of the "new"
-- operation for entities. Thus, if attributes have default values,
-- they are translated into `Maybe` types.
attr2NewCType :: String -> String -> Attribute -> CTypeExpr
attr2NewCType mName name (Attribute a adom _ anull) = case adom of
  IntDom    d  -> case a of
                   "Key" -> baseType (mName , (name++"ID"))
                   _     -> addMaybeIfNullOrDflt anull d intType
  FloatDom  d -> addMaybeIfNullOrDflt anull d floatType
  CharDom   d -> addMaybeIfNullOrDflt anull d (baseType (pre "Char"))
  StringDom _ -> stringType
  BoolDom   d -> addMaybeIfNullOrDflt anull d boolType
  DateDom   d -> addMaybeIfNullOrDflt anull d (baseType ("Time", "ClockTime"))
  KeyDom    k -> addMaybeIfNullOrDflt anull Nothing (baseType (mName, k++"ID"))
 where
  addMaybeIfNullOrDflt _      (Just _) texp = maybeType texp
  addMaybeIfNullOrDflt isnull Nothing  texp =
    if isnull then maybeType texp else texp

-- Translates an attribute type into a symbol used in an entity description.
attr2CSymbol :: Attribute -> CExpr
attr2CSymbol (Attribute _ adom _ _) = domain2CSymbol adom
 where
  domain2CSymbol :: Domain -> CExpr
  domain2CSymbol (IntDom    _) = CSymbol (mConn, "SQLTypeInt")
  domain2CSymbol (FloatDom  _) = CSymbol (mConn, "SQLTypeFloat")
  domain2CSymbol (CharDom   _) = CSymbol (mConn, "SQLTypeChar")
  domain2CSymbol (StringDom _) = CSymbol (mConn, "SQLTypeString")
  domain2CSymbol (BoolDom   _) = CSymbol (mConn, "SQLTypeBool")
  domain2CSymbol (DateDom   _) = CSymbol (mConn, "SQLTypeDate")
  domain2CSymbol (KeyDom    _) = CSymbol (mConn, "SQLTypeInt")
  
-- Generates operations to transform entity keys, like
-- id-to-value, id-to-int, show/read functions.
genKeyTransformFuncs :: String -> Entity -> [CFuncDecl]
genKeyTransformFuncs mName (Entity name attrs) =
  case head attrs of
     (Attribute "Key" _ PKey _ ) -> 
        [ stCmtFunc ("id-to-value function for entity `" ++ name ++ "`.")
            (mName, firstLow name ++ "ID") 1 Public
            (baseType (mName, name ++ "ID") ~> 
             applyTC ("Database.CDBI.Criteria", "Value") 
                     [baseType (mName, name ++ "ID")])
            [simpleRule [genAttrConvLeftOneTwo mName name (head attrs)]
                        (applyF ("Database.CDBI.Criteria", "idVal") 
                                [cvar "key"])]
        , stCmtFunc ("id-to-int function for entity `" ++ name ++ "`.")
            (mName, toKeyToInt $ firstLow name) 1 Public
            (baseType (mName, name ++"ID") ~> intType)
            [simpleRule [genAttrConvLeftOneTwo mName name (head attrs)]
                        (cvar "key")]
        , stCmtFunc (showKeyCmt name)
            (mName, "show" ++ name ++ "Key") 1 Public
            (baseType (mName, name) ~> stringType)
            [simpleRule [cpvar "entry"]
              (applyF (mER, "showDatabaseKey")
                [ string2ac name
                , constF (mName, toKeyToInt $ firstLow name)
                , applyF (mName, firstLow name ++ "Key") [cvar "entry"]
                ])]
        , stCmtFunc (readKeyCmt name)
            (mName, "read" ++ name ++ "Key") 0 Public
            (stringType ~> maybeType (baseType (mName, name ++ "ID")))
            [simpleRule []
              (applyF (mER, "readDatabaseKey")
                [ string2ac name, constF (mName, name ++ "ID")])]
        ]
     _  -> []
 where
  toKeyToInt s = s ++ "KeyToInt"

  showKeyCmt ename =
    "Shows the key of a `" ++ ename ++ "` entity as a string.\n" ++
    "This is useful if a textual representation of the key is necessary\n" ++
    "(e.g., as URL parameters in web pages), but it should no be used\n" ++
    "to store keys in other attributes!"

  readKeyCmt ename =
    "Transforms a string into a key of a `" ++ ename ++ "` entity.\n" ++
    "Nothing is returned if the string does not represent a meaningful key."

-- Generates operations to access and manipulate entries of entities
-- (as used by the Spicey web framework)
genEntryFuncs :: String -> Entity -> [CFuncDecl]
genEntryFuncs mName (Entity name attrs) =
  case head attrs of
     (Attribute "Key" _ PKey _ ) -> 
        [ stCmtFunc ("Gets all `" ++ name ++ "` entities.")
            (mName, "queryAll" ++ name ++ "s") 0 Public
            (applyTC (mConn, "DBAction")
                     [listType (baseType (mName, name))])
            [simpleRule []
               (applyF (mER, "getAllEntries") [constF endescr])]
        , stCmtFunc
            ("Gets all `" ++ name ++ "` entities satisfying a given predicate.")
            (mName, "queryCond" ++ name) 0 Public
            ((baseType (mName, name) ~> boolType) ~>
             applyTC (mConn, "DBAction")
                     [listType (baseType (mName, name))])
            [simpleRule []
               (applyF (mER, "getCondEntries") [constF endescr])]
        , stCmtFunc ("Gets a `" ++ name ++ "` entry by a given key.")
            (mName, "get" ++ name) 0 Public
            (baseType (mName, name ++ "ID") ~> 
             applyTC (mConn, "DBAction") [baseType (mName, name)])
            [simpleRule []
               (applyF (mER, "getEntryWithKey") 
                  [ constF endescr
                  , constF (mName, lname ++ "ColumnKey")
                  , constF (mName, lname ++ "ID")])]
        , let numargs = length attrs - 1
              args    = map ((++"_p") . firstLow . attributeName) (tail attrs)
              adoms   = map attributeDomain (tail attrs)
          in stCmtFunc ("Inserts a new `" ++ name ++ "` entity.")
            (mName, "new" ++ name ++ attrs2WithKeys) numargs Public
            (foldr (~>)
                   (applyTC (mConn, "DBAction") [baseType (mName, name)])
                   (map (attr2NewCType mName name) (tail attrs)))
            [simpleRule (map cpvar args)
               (applyF (mER, "insertNewEntry") 
                  [ constF endescr
                  , constF (mName, "set" ++ name ++ "Key")
                  , constF (mName, name ++ "ID")
                  , applyF (mName, name)
                     (applyF (mName, name ++ "ID") [cInt 0]
                      : map domVar2NewExp (zip adoms args))
                  ])]
        , stCmtFunc ("Deletes an existing `" ++ name ++ "` entry by its key.")
            (mName, "delete" ++ name) 0 Public
            (baseType (mName, name) ~> 
             applyTC (mConn, "DBAction") [unitType])
            [simpleRule []
               (applyF (mER, "deleteEntry") 
                  [ constF endescr
                  , constF (mName, lname ++ "ColumnKey")
                  , applyF (pre ".")
                      [constF (mName, lname ++ "ID"),
                       constF (mName, lname ++ "Key")]])]
        , stCmtFunc ("Updates an existing `" ++ name ++ "` entry by its key.")
            (mName, "update" ++ name) 0 Public
            (baseType (mName, name) ~> 
             applyTC (mConn, "DBAction") [unitType])
            [simpleRule []
               (applyF (mER, "updateEntry") [constF endescr ])]
        ]
     _  ->
      let numargs = length attrs
          args    = map (\i -> 'k' : show i) [1 .. numargs]
      in [ stCmtFunc ("Inserts a new `" ++ name ++ "` relation.")
            (mName, "new" ++ name) numargs Public
            (foldr (~>)
                   (applyTC (mConn, "DBAction") [unitType])
                   (map (getAttributeType mName name) attrs))
            [simpleRule (map cpvar args)
               (applyF (mER, "insertEntry") 
                  [ constF endescr
                  , applyF (mName, name) (map cvar args)
                  ])]
         , stCmtFunc ("Deletes an existing `" ++ name ++ "` relation.")
            (mName, "delete" ++ name) numargs Public
            (foldr (~>)
                   (applyTC (mConn, "DBAction") [unitType])
                   (map (getAttributeType mName name) attrs))
            [simpleRule (map cpvar args)
               (applyF (mER, "deleteEntryR") 
                  (constF endescr : concatMap attr2args (zip attrs args)))]
         , case attrs of
             [Attribute aname1 (KeyDom adom1) _ _,
              Attribute aname2 (KeyDom adom2) _ _] ->
              stCmtFunc ("Gets the associated `" ++ adom1 ++
                         "` entities for a given `" ++ adom2 ++ "` entity\n" ++
                         "w.r.t. the `" ++ name ++ "` relation.")
               (mName, "get" ++ adom1 ++ adom2 ++ "s") 1 Public
               (baseType (mName,adom1) ~>
                applyTC (mConn, "DBAction")
                        [listType (baseType (mName,adom2))])
               [simpleRule [cpvar "en"]
                 (applyF (mER,">+=")
                   [ applyF (mER, "getEntriesWithColVal") 
                       [ constF endescr
                       , constF (mName, lname ++ "Column" ++ aname1)
                       , applyF (mName, firstLow adom1 ++ "ID")
                           [applyF (mName, firstLow adom1 ++ "Key") [cvar "en"]]
                       ]
                   , CLambda [cpvar "vals"]
                       (applyF (pre "mapM")
                         [ constF (mName, "get" ++ adom2)
                         , applyF (pre "map")
                                  [ constF (mName, lname ++ aname2)
                                  , cvar "vals"]])
                   ])]
             _ -> error  $ "Non-binary relation entity " ++ name
      ]
 where
  lname   = firstLow name
  endescr = (mName, lname ++ "_CDBI_Description")
  
  attr2args (Attribute aname adom _ _, arg) =
    [ constF (mName, lname ++ "Column" ++ aname)
    , case adom of
        KeyDom en -> applyF (mName, firstLow en ++ "ID") [cvar arg]
        _ -> error $ "No KeyDom attribute in relation entity " ++ name
    ]

  attrs2WithKeys = concatMap (("With"++) . attributeName)
                             (filter isForeignKey attrs)

-- Translates an attribute domain and a variable into an expression.
-- If the domain has a default value, a maybe expression is generated.
domVar2NewExp :: (Domain, String) -> CExpr
domVar2NewExp (dom, v) = case dom of
  IntDom    (Just x) -> genMaybeWith (cInt x)
  FloatDom  (Just x) -> genMaybeWith (cFloat x)
  CharDom   (Just x) -> genMaybeWith (cChar x)
  BoolDom   (Just x) -> genMaybeWith (boolCExpr x)
  StringDom (Just x) -> applyF (pre "if_then_else")
                         [applyF (pre "null") [cvar v], string2ac x, cvar v]
  DateDom   (Just (CalendarTime yr mo dy hr mi sc tz)) ->
    genMaybeWith (applyF ("Time","toClockTime")
                    [applyF ("Time","CalendarTime")
                       [cInt yr, cInt mo, cInt dy,
                        cInt hr, cInt mi, cInt sc, cInt tz]])
  _ -> cvar v
 where
  genMaybeWith dflt = applyF (pre "maybe") [dflt, constF (pre "id"), cvar v]

-- Generates operations to create a new database with its schema.
genNewDBSchema :: String -> [Entity] -> [CFuncDecl]
genNewDBSchema mname ents =
  [ stCmtFunc
      ("Generates a new database (name provided as the parameter) and\n" ++
       "creates its schema.")
      (mname,"createNewDB") 1 Public
      (stringType ~> ioType unitType)
      [CRule [cpvar "dbfile"]
        (CSimpleRhs
          (CDoExpr [CSPat (cpvar "conn")
                          (applyF (mConn,"connectSQLite") [cvar "dbfile"]),
                    CSExpr (applyF (mConn,"writeConnection") [cvar "cstr", cvar "conn"]),
                    CSExpr (applyF (mConn,"disconnect") [cvar "conn"])])
          [CLocalPat (cpvar "cstr")
            (CSimpleRhs (applyF (pre "unlines")
                 [list2ac (map (string2ac . entity2createTable) ents)])
                        [])])]
  ]


-- Generates operations to save and restore the complete database.
genSaveDB :: String -> [Entity] -> [CFuncDecl]
genSaveDB mname ents =
  [ stCmtFunc
      ("Saves complete database as term files into an existing directory\n" ++
       "provided as a parameter.")
      (mname,"saveDBTo") 1 Public
      (stringType ~> ioType unitType)
      [simpleRule [cpvar "dir"] (CDoExpr (map saveDBTerms ents))]
  , stCmtFunc
      ("Restores complete database from term files which are stored\n" ++
       "in a directory provided as a parameter.")
      (mname,"restoreDBFrom") 1 Public
      (stringType ~> ioType unitType)
      [simpleRule [cpvar "dir"] (CDoExpr (map restoreDBTerms ents))]
  ]
 where
  saveDBTerms (Entity name _) = CSExpr $
    applyF (mER,"saveDBTerms")
           [ constF (mname, firstLow name ++ "_CDBI_Description")
           , constF (mname,"sqliteDBFile")
           , cvar "dir"]

  restoreDBTerms (Entity name _) = CSExpr $
    applyF (mER,"restoreDBTerms")
           [ constF (mname, firstLow name ++ "_CDBI_Description")
           , constF (mname,"sqliteDBFile")
           , cvar "dir"]

-- Generates runQ/runT operations (used by the Spicey web framework).
genRunFuncs :: String -> [CFuncDecl]
genRunFuncs mname =
  [ stCmtFunc "Runs a DB action (typically a query)."
      (mname,"runQ") 0 Public
      (applyTC (mConn, "DBAction") [ctvar "a"] ~> ioType (ctvar "a"))
      [simpleRule []
         (applyF (mER, "runQueryOnDB") [constF (mname,"sqliteDBFile")])]
  , stCmtFunc "Runs a DB action as a transaction."
      (mname,"runT") 0 Public
      (applyTC (mConn, "DBAction") [ctvar "a"] ~>
       ioType (applyTC (mConn,"SQLResult") [ctvar "a"]))
      [simpleRule []
         (applyF (mER, "runTransactionOnDB") [constF (mname,"sqliteDBFile")])]
  , stCmtFunc
      "Runs a DB action as a transaction. Emits an error in case of failure."
      (mname,"runJustT") 0 Public
      (applyTC (mConn, "DBAction") [ctvar "a"] ~> ioType (ctvar "a"))
      [simpleRule []
         (applyF (mER, "runJustTransactionOnDB")
                 [constF (mname,"sqliteDBFile")])]
  ]


----------------------------------------------------------------------------
--- Generates the `CREATE TABLE` SQL command for a given entity.
entity2createTable :: Entity -> String
entity2createTable (Entity name (a:atr)) = case a of
  Attribute "Key" _ _ _ ->
    "create table '" ++ name ++ "'(" ++
    foldl (\y x -> y ++ " ," ++ attr2colType x) (attr2colType a) atr ++
    ");"
  _ -> "create table '" ++ name ++ "'(" ++
       foldl (\y x -> y ++ " ," ++ relationship2colType x)
             (relationship2colType a)
             atr ++
       ", primary key (" ++ attr2combPrimaryKey (a:atr) ++ "));"

-- Transforms an attribute to the corresponding column type of the
-- database table (used when the first attribute of the entity
-- is named "Key" because the primary key will be that "Key" then).
attr2colType :: Attribute -> String
attr2colType (Attribute name ty key nullable) =
    "'" ++ name ++ "'" ++
    (case ty of
       IntDom Nothing -> ""
       IntDom _       -> " int"
       FloatDom _     -> " float"
       CharDom _      -> " char"
       StringDom _    -> " string"
       BoolDom _      -> " string" -- " boolean" -- no boolean type in SQLite3
       DateDom _      -> " string"
       KeyDom str     -> " int " ++ "REFERENCES '" ++ str ++ "'(Key)") ++
    (case key of
       PKey   -> " integer primary key"
       Unique -> " unique"
       NoKey  -> "") ++
    (case nullable of
       True  -> ""
       False -> if key == PKey then ""
                               else " not null")

-- Same as 'attr2colType' but for the case that the first attribute of the
-- entity is not named "Key", because there will be a combined primary key
-- so that the description is a little different.
relationship2colType :: Attribute -> String
relationship2colType (Attribute name ty key nullable) =
  "'" ++  name ++ "'" ++
  (case ty of
     IntDom _    -> " int"
     FloatDom _  -> " float "
     CharDom _   -> " char "
     StringDom _ -> " string "
     BoolDom _   -> " string " -- " boolean " -- no boolean type in SQLite3
     DateDom _   -> " string "
     KeyDom str    -> " int " ++ "REFERENCES '" ++ str ++"'(Key)") ++
  (case key of
     Unique -> " unique"
     _  -> "") ++
  (case nullable of
     True  -> ""
     False -> " not null")

-- Write a combined primary key
attr2combPrimaryKey :: [Attribute] -> String
attr2combPrimaryKey (Attribute name _ PKey _ : atr) =
  "'" ++ name ++ "'" ++
  (case attr2combPrimaryKey atr of
     "" -> ""
     x  -> ", " ++ x)
attr2combPrimaryKey (Attribute _ _ Unique _ : atr) = attr2combPrimaryKey atr
attr2combPrimaryKey (Attribute _ _ NoKey  _ : atr) = attr2combPrimaryKey atr
attr2combPrimaryKey [] = ""

----------------------------------------------------------------------------

firstLow :: String -> String
firstLow [] = []
firstLow (c:cs) = toLower c : cs

firstUp :: String -> String
firstUp [] = []
firstUp (c:cs) = toUpper c : cs

lowerCase :: String -> String
lowerCase s = map toLower s

-- A Boolean as an AbstractCurry expression.
boolCExpr :: Bool -> CExpr
boolCExpr b = constF (pre (if b then "True" else "False"))

----------------------------------------------------------------------------
