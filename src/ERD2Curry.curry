module ERD2Curry( main, erd2curryWithDBandERD, erd2cdbiWithDBandERD )
  where

import AbstractCurry.Files  (readCurry)
import AbstractCurry.Select (imports)
import AbstractCurry.Pretty
import Database.ERD
import Directory
import Distribution         ( curryCompiler, installDir )
import FilePath             ( (</>) )
import List                 ( isSuffixOf )
import System               ( exitWith, getArgs, setEnviron, system )
import Time
import XML

import Database.ERD.Goodies
import CodeGeneration
import ERD2CDBI             ( writeCDBI )
import ERD2Graph
import ERToolsPackageConfig ( packagePath, packageVersion, packageLoadPath )
import Transformation
import XML2ERD

systemBanner :: String
systemBanner =
  let bannerText = "ERD->Curry Compiler (Version " ++ packageVersion ++
                   " of 22/03/18)"
      bannerLine = take (length bannerText) (repeat '-')
   in bannerLine ++ "\n" ++ bannerText ++ "\n" ++ bannerLine

data EROptions = EROptions
  { optERProg    :: String  -- Curry program containing ERD
  , optFromXml   :: Bool    -- read ERD from XML file?
  , optVisualize :: Bool    -- visualize ERD?
  , optStorage   :: Storage -- storage of data
  , optToERDT    :: Bool    -- only transform into ERDT term file
  , optCDBI      :: Bool    -- generate Curry for Database.CDBI libraries
  }

defaultEROptions :: EROptions
defaultEROptions = EROptions
  { optERProg    = ""
  , optFromXml   = False
  , optVisualize = False
  , optStorage   = SQLite ""
  , optToERDT    = False
  , optCDBI      = False
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
parseArgs _ [] = return Nothing
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
  "--cdbi" -> parseArgs opts { optCDBI = True } args
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
  [ "Usage:"
  , ""
  , "    erd2curry [-l] [-d] [-t] [-x] [-v] [--db <dbfile>] [--cdbi] <prog>"
  , ""
  , "Parameters:"
  , "-l: generate interface to SQLite3 database (default)"
  , "-d: generate interface to SQL database (experimental)"
  , "-x: generate from ERD xmi document instead of ERD Curry program"
  , "-t: only transform ERD into ERDT term file"
  , "-v: only show visualization of ERD with dotty"
  , "--db <dbfile>: file of the SQLite3 database"
  , "--cdbi       : generate Curry module for Database.CDBI modules"
  , "<prog>       : name of Curry program file containing ERD definition"
  ]

--- Runs ERD2Curry with a given database and ERD term file or program.
erd2curryWithDBandERD :: String -> String -> IO ()
erd2curryWithDBandERD dbname erfile =
  startERD2Curry
    (Just defaultEROptions
             { optStorage = SQLite dbname, optERProg = erfile })

--- Runs ERD2CDBI with a given database, a Curry program file
--- containing ERD definition, and a target module name.
erd2cdbiWithDBandERD :: String -> String -> IO ()
erd2cdbiWithDBandERD dbname erprog =
  startERD2Curry
    (Just defaultEROptions
            { optStorage = SQLite dbname
            , optCDBI    = True
            , optERProg  = erprog })

startERD2Curry :: Maybe EROptions -> IO ()
startERD2Curry Nothing = do
  putStrLn $ "ERROR: Illegal arguments\n\n" ++ helpText
  exitWith 1
startERD2Curry (Just opts) = do
  -- set CURRYPATH in order to compile ERD model (which requires Database.ERD)
  unless (null packageLoadPath) $ setEnviron "CURRYPATH" packageLoadPath
  -- the directory containing the sources of this tool:
  let erd2currysrcdir = packagePath </> "src"
      orgfile         = optERProg opts
  erdfile <- if ".curry"  `isSuffixOf` orgfile ||
                ".lcurry" `isSuffixOf` orgfile
               then storeERDFromProgram orgfile
               else return orgfile
  if optVisualize opts
   then readERDTermFile erdfile >>= viewERD
   else start erd2currysrcdir opts erdfile "."

--- Main function to invoke the ERD->Curry translator.
start :: String -> EROptions -> String -> String -> IO ()
start erd2currysrcdir opts srcfile path = do
  (erdfile,erd) <- if optFromXml opts
                   then transformXmlFile srcfile path
                   else readERDTermFile srcfile >>= \e -> return (srcfile,e)
  let erdname      = erdName erd
      transerdfile = addPath path (erdname ++ "_ERDT.term")
      curryfile    = addPath path (erdname ++ ".curry")
      transerd     = transform erd
      opt          = ( if optStorage opts == SQLite ""
                         then SQLite (erdname ++ ".db")
                         else optStorage opts
                     , WithConsistencyTest )
      erdprog      = erd2code opt (transform erd)
  writeFile transerdfile
            ("{- ERD specification transformed from "++erdfile++" -}\n\n " ++
             showERD 2 transerd ++ "\n")
  putStrLn $ "Transformed ERD term written into file '"++transerdfile++"'."
  when (optCDBI opts) $
    writeCDBI srcfile transerd (storagePath (fst opt))
  unless (optToERDT opts || optCDBI opts) $ do
    copyAuxiliaryFiles
    moveOldVersion curryfile
    curdir <- getCurrentDirectory
    setCurrentDirectory path
    impprogs <- mapIO readCurry (imports erdprog)
    setCurrentDirectory curdir
    writeFile curryfile $
      prettyCurryProg
        (setOnDemandQualification (erdprog:impprogs) defaultOptions)
        erdprog
    putStrLn $ "Database operations generated into file '" ++ curryfile ++
               "'\nwith " ++ showOption opt ++ ".\n"
 where
  -- Copy auxiliary files ERDGeneric.curry and KeyDatabase.curry to target dir
  copyAuxiliaryFiles = do
    copyFile (erd2currysrcdir </> "ERDGeneric.curry")
             (addPath path "ERDGeneric.curry")

  showOption (Files f,_) = "database files stored in directory '"++f++"'"
  showOption (SQLite f,_) =
    "SQLite3 database stored in file '" ++ f ++ "'"
  showOption (DB,_) = "SQL database interface"

--- Adds a path to a file name.
addPath :: String -> String -> String
addPath path fname | path=="." = fname
                   | otherwise = path </> fname

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
   else done
 where
  calTime2Digits (CalendarTime y mo d h mi s _) =
    toD (y `mod` 100) ++ toD mo ++ toD d ++ toD h ++ toD mi ++ toD s

  toD i = if i<10 then '0':show i else show i
  

--- Read an ERD specification from an XML file in Umbrello format.
transformXmlFile :: String -> String -> IO (String,ERD)
transformXmlFile xmlfile path = do
  putStrLn $ "Reading XML file " ++ xmlfile ++ "..."
  xml <- readXmlFile xmlfile
  let erd     = convert xml
  let erdfile = addPath path (erdName erd ++ "_ERD.term")
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
