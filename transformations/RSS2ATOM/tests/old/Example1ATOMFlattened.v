(********************************************************************
	@name Coq declarations for model
	@date 2021/11/02 10:36:14
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.RSS2ATOM.ATOMFlattened.
Open Scope string_scope.


Definition InputModel : Model ATOMMetamodel_Object ATOMMetamodel_Link :=
	(Build_Model
		(
		(Build_ATOMMetamodel_Object EntryClass (BuildEntry  "La page du médecin" ""  None   (Some "")  None  "")) :: 
		(Build_ATOMMetamodel_Object AuthorClass (BuildAuthor  ""  None   (Some ""))) :: 
		(Build_ATOMMetamodel_Object EntryClass (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  "")) :: 
		(Build_ATOMMetamodel_Object LinkClass (BuildLink   None   (Some "http://www.atoute.org/page_du_medecin/spe/mg/mg_1024.htm")  None   None   None   (Some 0))) :: 
		(Build_ATOMMetamodel_Object LinkClass (BuildLink   None   (Some "http://www.atoute.org/medecine_pro.htm")  None   None   None   (Some 0))) :: 
		(Build_ATOMMetamodel_Object LinkClass (BuildLink   None   (Some "http://www.atoute.org/dictionnaire_medical.htm")  None   None   None   (Some 0))) :: 
		(Build_ATOMMetamodel_Object ATOMClass (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  "")) :: 
		(Build_ATOMMetamodel_Object EntryClass (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  "")) :: 
		(Build_ATOMMetamodel_Object LinkClass (BuildLink   None   (Some "http://www.atoute.org/")  None   None   None   (Some 0))) :: 
		nil)
		(
		(Build_ATOMMetamodel_Link EntryLinksReference (BuildEntryLinks (BuildEntry  "La page du médecin" ""  None   (Some "")  None  "") ((BuildLink   None   (Some "http://www.atoute.org/page_du_medecin/spe/mg/mg_1024.htm")  None   None   None   (Some 0)) :: nil ))) ::
		(Build_ATOMMetamodel_Link EntryCategoriesReference (BuildEntryCategories (BuildEntry  "La page du médecin" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAuthorsReference (BuildEntryAuthors (BuildEntry  "La page du médecin" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryContributorsReference (BuildEntryContributors (BuildEntry  "La page du médecin" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAtomReference (BuildEntryAtom (BuildEntry  "La page du médecin" ""  None   (Some "")  None  "") (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  ""))) ::
		(Build_ATOMMetamodel_Link AuthorAtomReference (BuildAuthorAtom (BuildAuthor  ""  None   (Some "")) (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  ""))) ::
		(Build_ATOMMetamodel_Link EntryLinksReference (BuildEntryLinks (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  "") ((BuildLink   None   (Some "http://www.atoute.org/medecine_pro.htm")  None   None   None   (Some 0)) :: nil ))) ::
		(Build_ATOMMetamodel_Link EntryCategoriesReference (BuildEntryCategories (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAuthorsReference (BuildEntryAuthors (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryContributorsReference (BuildEntryContributors (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAtomReference (BuildEntryAtom (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  "") (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  ""))) ::
		(Build_ATOMMetamodel_Link LinkEntryReference (BuildLinkEntry (BuildLink   None   (Some "http://www.atoute.org/page_du_medecin/spe/mg/mg_1024.htm")  None   None   None   (Some 0)) (BuildEntry  "La page du médecin" ""  None   (Some "")  None  ""))) ::
		(Build_ATOMMetamodel_Link LinkEntryReference (BuildLinkEntry (BuildLink   None   (Some "http://www.atoute.org/medecine_pro.htm")  None   None   None   (Some 0)) (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  ""))) ::
		(Build_ATOMMetamodel_Link LinkEntryReference (BuildLinkEntry (BuildLink   None   (Some "http://www.atoute.org/dictionnaire_medical.htm")  None   None   None   (Some 0)) (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  ""))) ::
		(Build_ATOMMetamodel_Link ATOMLinksReference (BuildATOMLinks (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  "") ((BuildLink   None   (Some "http://www.atoute.org/")  None   None   None   (Some 0)) :: nil ))) ::
		(Build_ATOMMetamodel_Link ATOMCategoriesReference (BuildATOMCategories (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  "")  nil )) ::
		(Build_ATOMMetamodel_Link ATOMAuthorsReference (BuildATOMAuthors (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  "") ((BuildAuthor  ""  None   (Some "")) :: nil ))) ::
		(Build_ATOMMetamodel_Link ATOMContributorsReference (BuildATOMContributors (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  "")  nil )) ::
		(Build_ATOMMetamodel_Link ATOMEntrieReference (BuildATOMEntrie (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  "") ((BuildEntry  "La page du médecin" ""  None   (Some "")  None  "") :: (BuildEntry  "Outils de recherche pour professionnels" ""  None   (Some "")  None  "") :: (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  "") :: nil ))) ::
		(Build_ATOMMetamodel_Link EntryLinksReference (BuildEntryLinks (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  "") ((BuildLink   None   (Some "http://www.atoute.org/dictionnaire_medical.htm")  None   None   None   (Some 0)) :: nil ))) ::
		(Build_ATOMMetamodel_Link EntryCategoriesReference (BuildEntryCategories (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAuthorsReference (BuildEntryAuthors (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryContributorsReference (BuildEntryContributors (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  "")  nil )) ::
		(Build_ATOMMetamodel_Link EntryAtomReference (BuildEntryAtom (BuildEntry  "Dictionnaires médicaux" ""  None   (Some "")  None  "") (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  ""))) ::
		(Build_ATOMMetamodel_Link LinkAtomReference (BuildLinkAtom (BuildLink   None   (Some "http://www.atoute.org/")  None   None   None   (Some 0)) (BuildATOM  "Atoute.org" ""  (Some "")  (Some "")  None   None  ""))) ::
		nil)
	).
