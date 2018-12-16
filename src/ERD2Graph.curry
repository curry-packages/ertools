---------------------------------------------------------------------
--- This module defines an operation to visualize an ERD term with dot.
---------------------------------------------------------------------

{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

module ERD2Graph(viewERD) where

import IO
import IOExts
import Char(isAlphaNum)
import List(intersperse)
import Database.ERD

import ShowDotGraph

-- Should a relation represented as an explicit node?
-- If not, it will be represented as an arc with a label.
-- However, some graph drawing tools have problems to write the
-- labels in a good manner to the arcs.
relationAsNode :: Bool
relationAsNode = True

-- Visualize an ERD term as aDot graph.
viewERD :: ERD -> IO ()
viewERD = viewDotGraph . erd2dot

-- Translate dependencies into Dot graph:
erd2dot :: ERD -> DotGraph
erd2dot (ERD erdname ens rels) =
  ugraph erdname (enodes++concat rnodes) (concat redges)
 where
  enodes = map entity2dot ens
  (rnodes,redges) = unzip (map relationship2dot rels)

  entity2dot (Entity ename attrs) =
    Node ename [("shape","record"),("style","bold"),
                ("label","{"++ename ++ "|" ++
                      concat (intersperse ("\\n") (map showAttr attrs))++"}")]

  showAttr (Attribute aname dom key isnull) =
    aname ++ " :: " ++ showDomain dom ++
    (if key==NoKey then "" else " / "++show key) ++
    (if isnull then " / null" else "")

  showDomain (IntDom _)        = "Int"
  showDomain (FloatDom _)      = "Float"
  showDomain (CharDom _)       = "Char"
  showDomain (StringDom _)     = "String"
  showDomain (BoolDom _)       = "Bool"
  showDomain (DateDom _)       = "Date"
  showDomain (UserDefined t _) = t
  showDomain (KeyDom _)        = "KeyDom"

  relationship2dot (Relationship rname [REnd en1 r1 c1, REnd en2 r2 c2]) =
    if relationAsNode
    then ([Node rname [("shape","diamond"),("style","filled")],
           Node (rname++r1) [("shape","plaintext"),("label",r1++"\\n"++showCard c1)],
           Node (rname++r2) [("shape","plaintext"),("label",r2++"\\n"++showCard c2)]],
          map (\ (n1,n2) -> Edge n1 n2 [])
              [(rname,rname++r1),(rname++r1,en1),
               (rname,rname++r2),(rname++r2,en2)])
    else ([Node rname [("shape","diamond"),("style","filled")]],
          [Edge rname en1 [("label",r1++"\\n"++showCard c1)],
           Edge rname en2 [("label",r2++"\\n"++showCard c2)]])

  showCard (Exactly n) = '(' : show n ++ "," ++ show n ++ ")"
  showCard (Between n Infinite) = '(' : show n ++ ",n)"
  showCard (Between n (Max m)) = '(' : show n ++ "," ++ show m ++ ")"

