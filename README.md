Curry-Tools for Dealing with Entity-Relationship Models for Databases
=====================================================================

This directory contains tools for dealing with database applications
specified by entity-relationship diagrams (ERDs) in Curry programs.

----------------------------------------------------------------------

ERD2CDBI compiler
-----------------

This tool transforms an ERD term into datatypes used in the
Database.CDBI. libraries. It also creates an information file
for the currypp SQL-Parser. This compiler is invoked by

    erd2curry --db <sqlite3 db file> --cdbi <Curry program with ERD>

----------------------------------------------------------------------

ERD2Curry compiler
------------------

This is a compiler for database applications
specified by entity-relationship diagrams (ERDs) into Curry programs.
The basic ideas and details about this approach are described in

B. Brassel, M. Hanus, M. Mueller:
High-Level Database Programming in Curry
In Proc. of the Tenth International Symposium on
Practical Aspects of Declarative Languages (PADL 2008),  pp. 316-332,
Springer LNCS 4902, 2008

Usage information:
------------------

Default use without Umbrello UML Modeller but ERD term descriptions:

1. Go to the directory where you want to create your Curry program and
   create an ERD description as a Curry term of type ERD
   (w.r.t. type definition given in module `Database.ERD`), e.g.,
   stored in `MyModel.curry`.

2. Compile it into a Curry program with

       erd2curry MyModel.curry

   This generates the auxiliary module `ERDGeneric.curry` and
   and a main module `<Model name>.curry>` containing the
   Curry API operations to the database.


Use with Umbrello UML Modeller (no longer actively supported):

1. Create an XML description of the ERD (with Umbrello)
   in xmi format, e.g., stored in "mymodel.xmi".

2. Compile it into a Curry program with

       erd2curry -x myerd.xmi


Visualization:
--------------

To visualize an ERD term file as a graph with dotty, execute

    erd2curry -v mymodel.erdterm


Examples:
---------

The directory `examples` contains two examples for the specification
of ERD models:

* `BlogERD.curry`: a simple ERD model for a blog with entries, comments,
  and tags.
* `UniERD.curry`: an ERD model for university lectures as
  presented in the original paper cited above.

---

Further infos and contact:

[Michael Hanus](http://www.michaelhanus.de/)
