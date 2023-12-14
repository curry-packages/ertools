module ERD2Curry
  ( main, startWithERD, EROptions(..), defaultEROptions
  , erd2CDBI, erd2curryWithDBandERD )
 where

import Control.Monad        ( when, unless )
import Data.List            ( isSuffixOf )
import System.Environment   ( getArgs, setEnv )

import AbstractCurry.Files     ( readCurry )
import AbstractCurry.Select    ( imports )
import AbstractCurry.Pretty
import AbstractCurry.Transform ( renameCurryModule )
import Database.ERD
import Data.Time
import System.Directory     ( doesFileExist, getModificationTime )
import System.Process       ( exitWith, system )
import XML                  ( readXmlFile )

import Database.ERD.FromXML
import Database.ERD.Goodies
import Database.ERD.ToCDBI  ( writeCDBI )
import Database.ERD.ToKeyDB
import Database.ERD.Transformation
import Database.ERD.View    ( viewERD )
import ERToolsPackageConfig ( packagePath, packageVersion, packageLoadPath )

systemBanner :: String
systemBanner =
  let bannerText = "ERD->Curry Compiler (Version " ++ packageVersion ++
                   " of 14/12/23)"
      bannerLine = take (length bannerText) (repeat '-')
   in bannerLine ++ "\n" ++ bannerText ++ "\n" ++ bannerLine

data EROptions = EROptions
  { optERProg    :: String  -- Curry program containing ERD
  , optFromXml   :: Bool    -- read ERD from XML file?
  , optVisualize :: Bool    -- visualize ERD?
  , optStorage   :: Storage -- storage of data
  , optToERDT    :: Bool    -- only transform into ERDT term file
  , optCDBI      :: Bool    -- generate Curry for Database.CDBI libraries
  , optModule    :: String  -- name of generated Curry module
  , optFile      :: String  -- file to store generated Curry module
  }

defaultEROptions :: EROptions
defaultEROptions = EROptions
  { optERProg    = ""
  , optFromXml   = False
  , optVisualize = False
  , optStorage   = SQLite ""
  , optToERDT    = False
  , optCDBI      = False
  , optModule    = ""
  , optFile      = ""
  }

--- Main function for saved state. The argument is the directory containing
--- these sources.
main :: IO ()
main = do
  putStrLn systemBanner
  args <- getArgs
  configs <- parseArgs defaultEROptions args
  startERD2Curry configs

parseArgs :: EROptions -> [String] -> IO (Maybe EROptions)
parseArgs _    []         = return Nothing
parseArgs opts (arg:args) = case arg of
  "-h" -> putStrLn helpText >> exitWith 0
  "-?" -> putStrLn helpText >> exitWith 0
  "--help" -> putStrLn helpText >> exitWith 0
  "-x" -> parseArgs opts { optFromXml = True } args
  "-l" -> parseArgs (setSQLite (optStorage opts)) args
  "-d" -> parseArgs opts { optStorage = DB } args
  "--db" -> if null args
              then return Nothing
              else parseArgs (setFilePath (head args) (optStorage opts))
                             (tail args)
  "-t" -> parseArgs opts { optToERDT = True } args
  "-v" -> parseArgs opts { optVisualize = True } args
  "--cdbi"   -> parseArgs opts { optCDBI = True } args
  "--module" -> if null args
                  then return Nothing
                  else parseArgs opts { optModule = head args } (tail args)
  "--outfile"-> if null args
                  then return Nothing
                  else parseArgs opts { optFile = head args } (tail args)
  f    -> return $ if null args then Just opts { optERProg = f }
                                else Nothing
 where
  setFilePath path (Files  _) = opts { optStorage = Files  path }
  setFilePath path (SQLite _) = opts { optStorage = SQLite path }
  setFilePath _    DB         = opts { optStorage = DB }

  setSQLite (Files  p) = opts { optStorage = SQLite p  }
  setSQLite (SQLite p) = opts { optStorage = SQLite p  }
  setSQLite DB         = opts { optStorage = SQLite "" }

storagePath :: Storage -> String
storagePath (Files  p) = p
storagePath (SQLite p) = p
storagePath DB         = ""

helpText :: String
helpText = unlines
  [ ""
  , "Usage:"
  , ""
  , "    erd2curry <options> <prog>"
  , ""
  , "with options:"
  , ""
  , "-l           : generate interface to SQLite3 database (default)"
  , "-d           : generate interface to SQL database (experimental)"
  , "-x           : generate from ERD xmi document instead of ERD Curry program"
  , "-t           : only transform ERD into ERDT term file"
  , "-v           : only show visualization of ERD with dotty"
  , "--db <dbfile>: file of the SQLite3 database"
  , "--cdbi       : generate Curry module for Database.CDBI modules"
  , "--module <m> : name of generated Curry module (default: <ERD name>)"
  , "--outfile <f>: file to store the generated module (default: <ERD name>.curry)"
  , "<prog>       : name of Curry program file containing ERD definition"
  ]

--- Runs ERD2Curry with a given database and ERD program.
erd2curryWithDBandERD :: String -> String -> IO ()
erd2curryWithDBandERD dbname erfile =
  startERD2Curry
    (Just defaultEROptions
             { optStorage = SQLite dbname, optERProg = erfile })

--- Translate an ERD into a Curry program using the API provided by the
--- Curry package `cdbi`. The parameters are the name of the database,
--- the name of the Curry program containing the ERD (only used in
--- a comment of the generated program), and the ERD definition.
--- The generated Curry module has the name of the ERD and
--- is put into the current directory.
erd2CDBI :: String -> String -> ERD -> IO ()
erd2CDBI dbname erdfile erd =
  startWithERD
    (defaultEROptions { optStorage = SQLite dbname, optCDBI = True })
    erdfile
    erd

startERD2Curry :: Maybe EROptions -> IO ()
startERD2Curry Nothing = do
  putStrLn $ "ERROR: Illegal arguments\n\n" ++ helpText
  exitWith 1
startERD2Curry (Just opts) = do
  -- set CURRYPATH in order to compile ERD model (which requires Database.ERD)
  unless (null packageLoadPath) $ setEnv "CURRYPATH" packageLoadPath
  -- the directory containing the sources of this tool:
  let orgfile = optERProg opts
  if optFromXml opts
    then do (_,erd) <- transformXmlFile orgfile
            startWithERD opts orgfile erd
    else do
      unless (".curry"  `isSuffixOf` orgfile ||
              ".lcurry" `isSuffixOf` orgfile) $ do
        putStrLn $ "ERROR: '" ++ orgfile ++ "' is not a Curry program file!"
        exitWith 1
      if optVisualize opts
        then readERDFromProgram orgfile >>= viewERD
        else readERDFromProgram orgfile >>= startWithERD opts orgfile

--- Main function to invoke the ERD->Curry translator.
--- The parameters are the tool options,
--- the name of the Curry program containing the ERD (only used in
--- a comment of the generated program), and the ERD definition.
--- If not changed by specific options, the generated Curry module
--- has the name of the ERD and is put into the current directory.
startWithERD :: EROptions -> String -> ERD -> IO ()
startWithERD opts srcfile erd = do
  let erdname      = erdName erd
      transerdfile = erdname ++ "_ERDT.term"
      curryfile    = if null (optFile opts) then erdname ++ ".curry"
                                            else optFile opts
      transerd     = transform erd
      opt          = ( if optStorage opts == SQLite ""
                         then SQLite (erdname ++ ".db")
                         else optStorage opts
                     , WithConsistencyTest )
      erdprog      = let prog = erd2code opt (transform erd)
                     in if null (optModule opts)
                          then prog
                          else renameCurryModule (optModule opts) prog
  writeFile transerdfile $
    "{- ERD specification transformed from " ++ srcfile ++ " -}\n\n " ++
    showERD 2 transerd ++ "\n"
  putStrLn $ "Transformed ERD term written into file '" ++ transerdfile ++ "'."
  when (optCDBI opts) $
    writeCDBI srcfile curryfile
              (if null (optModule opts) then erdname else optModule opts)
              transerd (storagePath (fst opt))
  unless (optToERDT opts || optCDBI opts) $ do
    moveOldVersion curryfile
    impprogs <- mapM readCurry (imports erdprog)
    writeFile curryfile $
      prettyCurryProg
        (setOnDemandQualification (erdprog:impprogs) defaultOptions)
        erdprog
    putStrLn $ unlines
      [ "Database operations generated into file '" ++ curryfile ++ "'"
      , "with " ++ showOption opt ++ "."
      , "NOTE: To compile this module, use packages " ++
        "'keydb', 'ertools' and 'time'." ]
 where
  showOption (Files f,_) = "database files stored in directory '"++f++"'"
  showOption (SQLite f,_) =
    "SQLite3 database stored in file '" ++ f ++ "'"
  showOption (DB,_) = "SQL database interface"

--- Moves a file (if it exists) to one with extension ".versYYMMDDhhmmss".
moveOldVersion :: String -> IO ()
moveOldVersion fname = do
  exists <- doesFileExist fname
  if exists
   then do
     mtime <- getModificationTime fname
     cmtime <- toCalendarTime mtime
     let fnamevers = fname ++ ".vers" ++ calTime2Digits cmtime
     system $ "mv "++fname++" "++fnamevers
     putStrLn $ "Old contents of file \""++fname++"\" saved into file \""++
                fnamevers++"\"."
   else return ()
 where
  calTime2Digits (CalendarTime y mo d h mi s _) =
    toD (y `mod` 100) ++ toD mo ++ toD d ++ toD h ++ toD mi ++ toD s

  toD i = if i<10 then '0':show i else show i
  

--- Read an ERD specification from an XML file in Umbrello format.
transformXmlFile :: String -> IO (String,ERD)
transformXmlFile xmlfile = do
  putStrLn $ "Reading XML file " ++ xmlfile ++ "..."
  xml <- readXmlFile xmlfile
  let erd     = convert xml
  let erdfile = erdName erd ++ "_ERD.term"
  writeFile erdfile
            ("{- ERD specification read from "++xmlfile++" -}\n\n " ++
             showERD 2 erd ++ "\n")
  putStrLn $ "ERD term written into file \""++erdfile++"\"."
  return (erdfile,erd)

{-
-- Uni.xmi -> ERD term:
(ERD "Uni"
 [(Entity "Student" [(Attribute "MatNum" (IntDom Nothing) PKey False),
                     (Attribute "Name" (StringDom Nothing) NoKey False),
                     (Attribute "Firstname" (StringDom Nothing) NoKey False),
                     (Attribute "Email" (UserDefined "MyModule.Email" Nothing) NoKey True)]),
  (Entity "Lecture" [(Attribute "Id" (IntDom Nothing) PKey False),
                     (Attribute "Title" (StringDom Nothing) Unique False),
                     (Attribute "Hours" (IntDom (Just 4)) NoKey False)]),
  (Entity "Lecturer" [(Attribute "Id" (IntDom Nothing) PKey False),
                      (Attribute "Name" (StringDom Nothing) NoKey False),
                      (Attribute "Firstname" (StringDom Nothing) NoKey False)]),
  (Entity "Group" [(Attribute "Time" (StringDom Nothing) NoKey False)])]
 [(Relationship "Teaching" [(REnd "Lecturer" "taught_by" (Exactly 1)),
                            (REnd "Lecture" "teaches" (Between 0 Infinite))]),
  (Relationship "Participation" [(REnd "Student" "participated_by" (Between 0 Infinite)),
                                 (REnd "Lecture" "participates" (Between 0 Infinite))]),
  (Relationship "Membership" [(REnd "Student" "consists_of" (Exactly 3)),
                              (REnd "Group" "member_of" (Between 0 Infinite))])])

-- Transformation of ERD term:
(ERD "Uni"
 [(Entity "Membership"
          [(Attribute "Student_Membership_Key" (KeyDom "Student") PKey False),
           (Attribute "Group_Membership_Key" (KeyDom "Group") PKey False)]),
  (Entity "Participation"
          [(Attribute "Student_Participation_Key" (KeyDom "Student") PKey False),
           (Attribute "Lecture_Participation_Key" (KeyDom "Lecture") PKey False)]),
  (Entity "Student"
          [(Attribute "Key" (IntDom Nothing) PKey False),
           (Attribute "MatNum" (IntDom Nothing) Unique False),
           (Attribute "Name" (StringDom Nothing) NoKey False),
           (Attribute "Firstname" (StringDom Nothing) NoKey False),
           (Attribute "Email" (UserDefined "MyModule.Email" Nothing) NoKey True)]),
  (Entity "Lecture"
          [(Attribute "Key" (IntDom Nothing) PKey False),
           (Attribute "Lecturer_Teaching_Key" (KeyDom "Lecturer") NoKey False),
           (Attribute "Id" (IntDom Nothing) Unique False),
           (Attribute "Title" (StringDom Nothing) Unique False),
           (Attribute "Hours" (IntDom (Just 4)) NoKey False)]),
  (Entity "Lecturer"
          [(Attribute "Key" (IntDom Nothing) PKey False),
           (Attribute "Id" (IntDom Nothing) Unique False),
           (Attribute "Name" (StringDom Nothing) NoKey False),
           (Attribute "Firstname" (StringDom Nothing) NoKey False)]),
  (Entity "Group"
          [(Attribute "Key" (IntDom Nothing) PKey False),
           (Attribute "Time" (StringDom Nothing) NoKey False)])]
 [(Relationship [] [(REnd "Student" [] (Exactly 1)),
                    (REnd "Membership" "member_of" (Between 0 Infinite))]),
  (Relationship [] [(REnd "Group" [] (Exactly 1)),
                    (REnd "Membership" "consists_of" (Exactly 3))]),
  (Relationship [] [(REnd "Student" [] (Exactly 1)),
                    (REnd "Participation" "participates" (Between 0 Infinite))]),
  (Relationship [] [(REnd "Lecture" [] (Exactly 1)),
                    (REnd "Participation" "participated_by" (Between 0 Infinite))]),
  (Relationship "Teaching" [(REnd "Lecturer" "taught_by" (Exactly 1)),
                            (REnd "Lecture" "teaches" (Between 0 Infinite))])])
-}
