import Database.ERD -- from package cdbi

blogERD :: ERD
blogERD =
 ERD "Blog" 
     [Entity "Entry" 
          [Attribute "Title"  (StringDom Nothing) Unique False, 
           Attribute "Text"   (StringDom Nothing) NoKey  False,
           Attribute "Author" (StringDom Nothing) NoKey  False,
           Attribute "Date"   (DateDom   Nothing) NoKey  False],
      Entity "Comment"
        [Attribute "Text"   (StringDom Nothing) NoKey False,
         Attribute "Author" (StringDom Nothing) NoKey False,
         Attribute "Date"   (DateDom   Nothing) NoKey False],
      Entity "Tag"
        [Attribute "Name" (StringDom Nothing) Unique False]
     ]
     [Relationship "Commenting"
       [REnd "Entry"   "commentsOn"    (Exactly 1),
        REnd "Comment" "isCommentedBy" (Between 0 Infinite)],
      Relationship "Tagging"
       [REnd "Entry" "tags" (Between 0 Infinite),
        REnd "Tag" "tagged" (Between 0 Infinite)]
     ]
