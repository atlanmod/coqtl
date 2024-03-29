(********************************************************************
	@name Coq declarations for model
	@date 2021/11/24 11:24:50
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.RSS2ATOM.ATOM.
Open Scope string_scope.


Definition ExempleATOM : Model ATOMMetamodel_Object ATOMMetamodel_Link :=
	(Build_Model
		(
		(Build_ATOMMetamodel_Object AuthorClass (BuildAuthor (BuildPerson  "John Doe"  (Some "")  (Some "johndoe@example.com")) )) :: 
		(Build_ATOMMetamodel_Object EntryClass (BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z")) :: 
		(Build_ATOMMetamodel_Object LinkClass (BuildLink   (Some "")  (Some "http://example.org")  (Some "")  (Some "")  (Some "")  (Some 0))) :: 
		(Build_ATOMMetamodel_Object LinkClass (BuildLink   (Some "")  (Some "http://example.org/2003/12/13/atom03")  (Some "")  (Some "")  (Some "")  (Some 0))) :: 
		(Build_ATOMMetamodel_Object CategoryClass (BuildCategory  "Film"  (Some "lesheme1")  (Some "lelabel"))) :: 
		(Build_ATOMMetamodel_Object ATOMClass (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z")) :: 
		(Build_ATOMMetamodel_Object CategoryClass (BuildCategory  "Movie"  (Some "lesheme2")  (Some "lelabel"))) :: 
		nil)
		(
		(Build_ATOMMetamodel_Link AuthorAtomReference (BuildAuthorAtom (BuildAuthor (BuildPerson  "John Doe"  (Some "")  (Some "johndoe@example.com")) ) (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z"))) ::
		(Build_ATOMMetamodel_Link EntryLinksReference (BuildEntryLinks (BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z") ((BuildLink   (Some "")  (Some "http://example.org/2003/12/13/atom03")  (Some "")  (Some "")  (Some "")  (Some 0)) :: nil ))) ::
		(Build_ATOMMetamodel_Link EntryCategoriesReference (BuildEntryCategories (BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAuthorsReference (BuildEntryAuthors (BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z")  nil )) ::
		(Build_ATOMMetamodel_Link EntryContributorsReference (BuildEntryContributors (BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAtomReference (BuildEntryAtom (BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z") (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z"))) ::
		(Build_ATOMMetamodel_Link LinkAtomReference (BuildLinkAtom (BuildLink   (Some "")  (Some "http://example.org")  (Some "")  (Some "")  (Some "")  (Some 0)) (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z"))) ::
		(Build_ATOMMetamodel_Link LinkEntryReference (BuildLinkEntry (BuildLink   (Some "")  (Some "http://example.org/2003/12/13/atom03")  (Some "")  (Some "")  (Some "")  (Some 0)) (BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z"))) ::
		(Build_ATOMMetamodel_Link CategoryAtomReference (BuildCategoryAtom (BuildCategory  "Film"  (Some "lesheme1")  (Some "lelabel")) (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z"))) ::
		(Build_ATOMMetamodel_Link ATOMLinksReference (BuildATOMLinks (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z") ((BuildLink   (Some "")  (Some "http://example.org")  (Some "")  (Some "")  (Some "")  (Some 0)) :: nil ))) ::
		(Build_ATOMMetamodel_Link ATOMCategoriesReference (BuildATOMCategories (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z") ((BuildCategory  "Film"  (Some "lesheme1")  (Some "lelabel")) :: (BuildCategory  "Movie"  (Some "lesheme2")  (Some "lelabel")) :: nil ))) ::
		(Build_ATOMMetamodel_Link ATOMAuthorsReference (BuildATOMAuthors (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z") ((BuildAuthor (BuildPerson  "John Doe"  (Some "")  (Some "johndoe@example.com")) ) :: nil ))) ::
		(Build_ATOMMetamodel_Link ATOMContributorsReference (BuildATOMContributors (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z")  nil )) ::
		(Build_ATOMMetamodel_Link ATOMEntrieReference (BuildATOMEntrie (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z") ((BuildEntry  "Atom-Powered Robots Run Amok" "urn:uuid:1225c695-cfb8-4ebb-aaaa-80da344efa6a"  (Some "")  (Some "Some text.")  None  "2003-12-13T18:30:02Z") :: nil ))) ::
		(Build_ATOMMetamodel_Link CategoryAtomReference (BuildCategoryAtom (BuildCategory  "Movie"  (Some "lesheme2")  (Some "lelabel")) (BuildATOM  "Example ATOM" "urn:uuid:60a76c80-d399-11d9-b91C-0003939e0af6"  (Some "Insert witty or insightful remark here")  (Some "")  (Some "")  (Some "") "2003-12-13T18:30:02Z"))) ::
		nil)
	).
