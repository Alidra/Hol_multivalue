Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4373817_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem4373539 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4373540 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4373541 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4373540 _103718 _103721 x) (@lem4373539 _103718 _103721 x)). Qed.
Lemma lem4373542 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4373541 _103718 _103721 x y). Qed.
Lemma lem4373543 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4373544 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4373543 _103718 _103721 x y) (@lem4373542 _103718 _103721 x y)). Qed.
Lemma lem4373545 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4373544 _103718 _103721 x y s). Qed.
Lemma lem4373546 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4373547 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4373546 _103718 _103721 x s y) (@lem4373545 _103718 _103721 x y s)). Qed.
Lemma lem4373548 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4373547 _103718 _103721 x s y t). Qed.
Lemma lem4373549 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4373575 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4373576 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem4373575 _83095 p). Qed.
Lemma lem4373577 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem4373578 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem4373577 _83095 p) (@lem4373576 _83095 p)). Qed.
Lemma lem4373579 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem4373578 _83095 p x). Qed.
Lemma lem4373580 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem4373589 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term14 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4373590 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = ((term15 _5106 _5107 P) = (term16 _5106 _5107 P)).
Proof. exact (eq_refl (term14 _5106 _5107 P)). Qed.
Lemma lem4373592 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4373593 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4373594 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4373593 A s) (@lem4373592 A s)). Qed.
Lemma lem4373595 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4373594 A s t). Qed.
Lemma lem4373596 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4373613 {_89711 _89725 : Type'} : term21 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem4373614 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term22 _89711 _89725 P.
Proof. exact (@lem4373613 _89711 _89725 P). Qed.
Lemma lem4373615 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term22 _89711 _89725 P) = (term23 _89711 _89725 P).
Proof. exact (eq_refl (term22 _89711 _89725 P)). Qed.
Lemma lem4373616 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term23 _89711 _89725 P.
Proof. exact (EQ_MP (@lem4373615 _89711 _89725 P) (@lem4373614 _89711 _89725 P)). Qed.
Lemma lem4373617 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term24 _89711 _89725 P f.
Proof. exact (@lem4373616 _89711 _89725 P f). Qed.
Lemma lem4373618 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term24 _89711 _89725 P f) = ((term25 _89711 _89725 P f) = (term26 _89711 _89725 P f)).
Proof. exact (eq_refl (term24 _89711 _89725 P f)). Qed.
Lemma lem4373636 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4373596 A s t) (@lem4373595 A s t)). Qed.
Lemma lem4373637 {_104960 _104961 : Type'} (s : type1210 _104960 _104961) (t : type1210 _104960 _104961) : (s = t) = (term27 _104960 _104961 s t).
Proof. exact (@lem4373636 (prod _104960 _104961) s t). Qed.
Lemma lem4373638 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term28 _104960 _104961 s f) = (term29 _104960 _104961 f s)) = (term30 _104960 _104961 f s).
Proof. exact (@lem4373637 _104960 _104961 (term28 _104960 _104961 s f) (term29 _104960 _104961 f s)). Qed.
Lemma lem4373644 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = (term16 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4373590 _5106 _5107 P) (@lem4373589 _5106 _5107 P)). Qed.
Lemma lem4373645 {_104960 _104961 : Type'} (P : type1210 _104960 _104961) : (term31 _104960 _104961 P) = (term32 _104960 _104961 P).
Proof. exact (@lem4373644 _104961 _104960 P). Qed.
Lemma lem4373646 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term33 _104960 _104961 f s) = (term34 _104960 _104961 f s).
Proof. exact (@lem4373645 _104960 _104961 (term35 _104960 _104961 f s)). Qed.
Lemma lem4373647 {_104960 _104961 : Type'} (x : prod _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term36 _104960 _104961 f s x) = ((term37 _104960 _104961 x s f) = (term38 _104960 _104961 x f s)).
Proof. exact (eq_refl (term36 _104960 _104961 f s x)). Qed.
Lemma lem4373648 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term39 _104960 _104961 f s) = (term35 _104960 _104961 f s).
Proof. exact (fun_ext (fun x : prod _104960 _104961 => @lem4373647 _104960 _104961 x f s)). Qed.
Lemma lem4373649 {_104960 _104961 : Type'} : (@all (prod _104960 _104961)) = (@all (prod _104960 _104961)).
Proof. exact (eq_refl (@all (prod _104960 _104961))). Qed.
Lemma lem4373650 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term33 _104960 _104961 f s) = (term30 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373649 _104960 _104961) (@lem4373648 _104960 _104961 f s)). Qed.
Lemma lem4373651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373652 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term40 _104960 _104961 f s) = (term41 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373651) (@lem4373650 _104960 _104961 f s)). Qed.
Lemma lem4373653 {_104960 _104961 : Type'} (p1 : _104960) (p2 : _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term42 _104960 _104961 f s p1 p2) = ((term43 _104960 _104961 p1 p2 s f) = (term44 _104960 _104961 p1 p2 f s)).
Proof. exact (eq_refl (term42 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4373654 {_104960 _104961 : Type'} (p1 : _104960) (f : type686 _104961) (s : _104960 -> Prop) : (term45 _104960 _104961 f s p1) = (term46 _104960 _104961 p1 f s).
Proof. exact (fun_ext (fun p2 : _104961 => @lem4373653 _104960 _104961 p1 p2 f s)). Qed.
Lemma lem4373655 {_104961 : Type'} : (@all _104961) = (@all _104961).
Proof. exact (eq_refl (@all _104961)). Qed.
Lemma lem4373656 {_104960 _104961 : Type'} (p1 : _104960) (f : type686 _104961) (s : _104960 -> Prop) : (term47 _104960 _104961 f s p1) = (term48 _104960 _104961 p1 f s).
Proof. exact (MK_COMB (@lem4373655 _104961) (@lem4373654 _104960 _104961 p1 f s)). Qed.
Lemma lem4373657 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term49 _104960 _104961 f s) = (term50 _104960 _104961 f s).
Proof. exact (fun_ext (fun p1 : _104960 => @lem4373656 _104960 _104961 p1 f s)). Qed.
Lemma lem4373658 {_104960 : Type'} : (@all _104960) = (@all _104960).
Proof. exact (eq_refl (@all _104960)). Qed.
Lemma lem4373659 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term34 _104960 _104961 f s) = (term51 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373658 _104960) (@lem4373657 _104960 _104961 f s)). Qed.
Lemma lem4373660 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term33 _104960 _104961 f s) = (term34 _104960 _104961 f s)) = ((term30 _104960 _104961 f s) = (term51 _104960 _104961 f s)).
Proof. exact (MK_COMB (@lem4373652 _104960 _104961 f s) (@lem4373659 _104960 _104961 f s)). Qed.
Lemma lem4373661 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term30 _104960 _104961 f s) = (term51 _104960 _104961 f s).
Proof. exact (EQ_MP (@lem4373660 _104960 _104961 f s) (@lem4373646 _104960 _104961 f s)). Qed.
Lemma lem4373668 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term28 _104960 _104961 s f) = (term29 _104960 _104961 f s)) = (term51 _104960 _104961 f s).
Proof. exact (TRANS (@lem4373638 _104960 _104961 f s) (@lem4373661 _104960 _104961 f s)). Qed.
Lemma lem4373680 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373549 _103718 _103721 x s y t) (@lem4373548 _103718 _103721 x s y t)). Qed.
Lemma lem4373681 {_104960 _104961 : Type'} (x : _104960) (s : _104960 -> Prop) (y : _104961) (t : _104961 -> Prop) : (term7 _104960 _104961 x y s t) = (term8 _104960 _104961 x s y t).
Proof. exact (@lem4373680 _104960 _104961 x s y t). Qed.
Lemma lem4373682 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (f : type686 _104961) : (term43 _104960 _104961 p1 p2 s f) = (term52 _104960 _104961 p1 s p2 f).
Proof. exact (@lem4373681 _104960 _104961 p1 s p2 (@INTERS _104961 f)). Qed.
Lemma lem4373685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373686 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (f : type686 _104961) : (term53 _104960 _104961 p1 p2 s f) = (term54 _104960 _104961 p1 s p2 f).
Proof. exact (MK_COMB (@lem4373685) (@lem4373682 _104960 _104961 p1 s p2 f)). Qed.
Lemma lem4373688 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term25 _89711 _89725 P f) = (term26 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem4373618 _89711 _89725 P f) (@lem4373617 _89711 _89725 P f)). Qed.
Lemma lem4373689 {_104960 _104961 : Type'} (P : type686 _104961) (f : type857 _104960 _104961) : (term55 _104960 _104961 P f) = (term56 _104960 _104961 P f).
Proof. exact (@lem4373688 (prod _104960 _104961) (_104961 -> Prop) P f). Qed.
Lemma lem4373690 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term57 _104960 _104961 f s) = (term58 _104960 _104961 f s).
Proof. exact (@lem4373689 _104960 _104961 (term59 _104961 f) (term60 _104960 _104961 s)). Qed.
Lemma lem4373691 {_104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) : (term61 _104961 f t) = (@IN (_104961 -> Prop) t f).
Proof. exact (eq_refl (term61 _104961 f t)). Qed.
Lemma lem4373692 {_104960 _104961 : Type'} (GEN_PVAR_137 : type1210 _104960 _104961) : (@SETSPEC ((prod _104960 _104961) -> Prop) GEN_PVAR_137) = (@SETSPEC ((prod _104960 _104961) -> Prop) GEN_PVAR_137).
Proof. exact (eq_refl (@SETSPEC ((prod _104960 _104961) -> Prop) GEN_PVAR_137)). Qed.
Lemma lem4373693 {_104960 _104961 : Type'} (GEN_PVAR_137 : type1210 _104960 _104961) (t : _104961 -> Prop) (f : type686 _104961) : (term62 _104960 _104961 GEN_PVAR_137 f t) = (term63 _104960 _104961 GEN_PVAR_137 t f).
Proof. exact (MK_COMB (@lem4373692 _104960 _104961 GEN_PVAR_137) (@lem4373691 _104961 t f)). Qed.
Lemma lem4373694 {_104960 _104961 : Type'} (s : _104960 -> Prop) (t : _104961 -> Prop) : (term64 _104960 _104961 s t) = (@CROSS _104961 _104960 s t).
Proof. exact (eq_refl (term64 _104960 _104961 s t)). Qed.
Lemma lem4373695 {_104960 _104961 : Type'} (GEN_PVAR_137 : type1210 _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) (t : _104961 -> Prop) : (term65 _104960 _104961 GEN_PVAR_137 f s t) = (term66 _104960 _104961 GEN_PVAR_137 f s t).
Proof. exact (MK_COMB (@lem4373693 _104960 _104961 GEN_PVAR_137 t f) (@lem4373694 _104960 _104961 s t)). Qed.
Lemma lem4373696 {_104960 _104961 : Type'} (GEN_PVAR_137 : type1210 _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term67 _104960 _104961 GEN_PVAR_137 f s) = (term68 _104960 _104961 GEN_PVAR_137 f s).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4373695 _104960 _104961 GEN_PVAR_137 f s t)). Qed.
Lemma lem4373697 {_104961 : Type'} : (@ex (_104961 -> Prop)) = (@ex (_104961 -> Prop)).
Proof. exact (eq_refl (@ex (_104961 -> Prop))). Qed.
Lemma lem4373698 {_104960 _104961 : Type'} (GEN_PVAR_137 : type1210 _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term69 _104960 _104961 GEN_PVAR_137 f s) = (term70 _104960 _104961 GEN_PVAR_137 f s).
Proof. exact (MK_COMB (@lem4373697 _104961) (@lem4373696 _104960 _104961 GEN_PVAR_137 f s)). Qed.
Lemma lem4373699 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term71 _104960 _104961 f s) = (term72 _104960 _104961 f s).
Proof. exact (fun_ext (fun GEN_PVAR_137 : type1210 _104960 _104961 => @lem4373698 _104960 _104961 GEN_PVAR_137 f s)). Qed.
Lemma lem4373700 {_104960 _104961 : Type'} : (@GSPEC ((prod _104960 _104961) -> Prop)) = (@GSPEC ((prod _104960 _104961) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _104960 _104961) -> Prop))). Qed.
Lemma lem4373701 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term73 _104960 _104961 f s) = (term74 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373700 _104960 _104961) (@lem4373699 _104960 _104961 f s)). Qed.
Lemma lem4373702 {_104960 _104961 : Type'} : (@INTERS (prod _104960 _104961)) = (@INTERS (prod _104960 _104961)).
Proof. exact (eq_refl (@INTERS (prod _104960 _104961))). Qed.
Lemma lem4373703 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term57 _104960 _104961 f s) = (term29 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373702 _104960 _104961) (@lem4373701 _104960 _104961 f s)). Qed.
Lemma lem4373704 {_104960 _104961 : Type'} : (@eq ((prod _104960 _104961) -> Prop)) = (@eq ((prod _104960 _104961) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _104960 _104961) -> Prop))). Qed.
Lemma lem4373705 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term75 _104960 _104961 f s) = (term76 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373704 _104960 _104961) (@lem4373703 _104960 _104961 f s)). Qed.
Lemma lem4373706 {_104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) : (term61 _104961 f t) = (@IN (_104961 -> Prop) t f).
Proof. exact (eq_refl (term61 _104961 f t)). Qed.
Lemma lem4373707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4373708 {_104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) : (term77 _104961 f t) = (term78 _104961 t f).
Proof. exact (MK_COMB (@lem4373707) (@lem4373706 _104961 t f)). Qed.
Lemma lem4373709 {_104960 _104961 : Type'} (s : _104960 -> Prop) (t : _104961 -> Prop) : (term64 _104960 _104961 s t) = (@CROSS _104961 _104960 s t).
Proof. exact (eq_refl (term64 _104960 _104961 s t)). Qed.
Lemma lem4373710 {_104960 _104961 : Type'} (a : prod _104960 _104961) : (@IN (prod _104960 _104961) a) = (@IN (prod _104960 _104961) a).
Proof. exact (eq_refl (@IN (prod _104960 _104961) a)). Qed.
Lemma lem4373711 {_104960 _104961 : Type'} (a : prod _104960 _104961) (s : _104960 -> Prop) (t : _104961 -> Prop) : (term79 _104960 _104961 a s t) = (term80 _104960 _104961 a s t).
Proof. exact (MK_COMB (@lem4373710 _104960 _104961 a) (@lem4373709 _104960 _104961 s t)). Qed.
Lemma lem4373712 {_104960 _104961 : Type'} (f : type686 _104961) (a : prod _104960 _104961) (s : _104960 -> Prop) (t : _104961 -> Prop) : (term81 _104960 _104961 f a s t) = (term82 _104960 _104961 f a s t).
Proof. exact (MK_COMB (@lem4373708 _104961 t f) (@lem4373711 _104960 _104961 a s t)). Qed.
Lemma lem4373713 {_104960 _104961 : Type'} (f : type686 _104961) (a : prod _104960 _104961) (s : _104960 -> Prop) : (term83 _104960 _104961 f a s) = (term84 _104960 _104961 f a s).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4373712 _104960 _104961 f a s t)). Qed.
Lemma lem4373714 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4373715 {_104960 _104961 : Type'} (f : type686 _104961) (a : prod _104960 _104961) (s : _104960 -> Prop) : (term85 _104960 _104961 f a s) = (term86 _104960 _104961 f a s).
Proof. exact (MK_COMB (@lem4373714 _104961) (@lem4373713 _104960 _104961 f a s)). Qed.
Lemma lem4373716 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) : (@SETSPEC (prod _104960 _104961) GEN_PVAR_56) = (@SETSPEC (prod _104960 _104961) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _104960 _104961) GEN_PVAR_56)). Qed.
Lemma lem4373717 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (a : prod _104960 _104961) (s : _104960 -> Prop) : (term87 _104960 _104961 GEN_PVAR_56 f a s) = (term88 _104960 _104961 GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem4373716 _104960 _104961 GEN_PVAR_56) (@lem4373715 _104960 _104961 f a s)). Qed.
Lemma lem4373718 {_104960 _104961 : Type'} (a : prod _104960 _104961) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4373719 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) (a : prod _104960 _104961) : (term89 _104960 _104961 GEN_PVAR_56 f s a) = (term90 _104960 _104961 GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem4373717 _104960 _104961 GEN_PVAR_56 f a s) (@lem4373718 _104960 _104961 a)). Qed.
Lemma lem4373720 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term91 _104960 _104961 GEN_PVAR_56 f s) = (term92 _104960 _104961 GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : prod _104960 _104961 => @lem4373719 _104960 _104961 GEN_PVAR_56 f s a)). Qed.
Lemma lem4373721 {_104960 _104961 : Type'} : (@ex (prod _104960 _104961)) = (@ex (prod _104960 _104961)).
Proof. exact (eq_refl (@ex (prod _104960 _104961))). Qed.
Lemma lem4373722 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term93 _104960 _104961 GEN_PVAR_56 f s) = (term94 _104960 _104961 GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem4373721 _104960 _104961) (@lem4373720 _104960 _104961 GEN_PVAR_56 f s)). Qed.
Lemma lem4373723 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term95 _104960 _104961 f s) = (term96 _104960 _104961 f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _104960 _104961 => @lem4373722 _104960 _104961 GEN_PVAR_56 f s)). Qed.
Lemma lem4373724 {_104960 _104961 : Type'} : (@GSPEC (prod _104960 _104961)) = (@GSPEC (prod _104960 _104961)).
Proof. exact (eq_refl (@GSPEC (prod _104960 _104961))). Qed.
Lemma lem4373725 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term58 _104960 _104961 f s) = (term97 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373724 _104960 _104961) (@lem4373723 _104960 _104961 f s)). Qed.
Lemma lem4373726 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term57 _104960 _104961 f s) = (term58 _104960 _104961 f s)) = ((term29 _104960 _104961 f s) = (term97 _104960 _104961 f s)).
Proof. exact (MK_COMB (@lem4373705 _104960 _104961 f s) (@lem4373725 _104960 _104961 f s)). Qed.
Lemma lem4373727 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term29 _104960 _104961 f s) = (term97 _104960 _104961 f s).
Proof. exact (EQ_MP (@lem4373726 _104960 _104961 f s) (@lem4373690 _104960 _104961 f s)). Qed.
Lemma lem4373740 {_104960 _104961 : Type'} (p1 : _104960) (p2 : _104961) : (term98 _104960 _104961 p1 p2) = (term98 _104960 _104961 p1 p2).
Proof. exact (eq_refl (term98 _104960 _104961 p1 p2)). Qed.
Lemma lem4373741 {_104960 _104961 : Type'} (p1 : _104960) (p2 : _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term44 _104960 _104961 p1 p2 f s) = (term99 _104960 _104961 p1 p2 f s).
Proof. exact (MK_COMB (@lem4373740 _104960 _104961 p1 p2) (@lem4373727 _104960 _104961 f s)). Qed.
Lemma lem4373743 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4373580 _83095 p x) (@lem4373579 _83095 p x)). Qed.
Lemma lem4373744 {_104960 _104961 : Type'} (p : type1210 _104960 _104961) (x : prod _104960 _104961) : (term100 _104960 _104961 x p) = (p x).
Proof. exact (@lem4373743 (prod _104960 _104961) p x). Qed.
Lemma lem4373745 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) (p1 : _104960) (p2 : _104961) : (term101 _104960 _104961 p1 p2 f s) = (term102 _104960 _104961 f s p1 p2).
Proof. exact (@lem4373744 _104960 _104961 (term103 _104960 _104961 f s) (@pair _104960 _104961 p1 p2)). Qed.
Lemma lem4373746 {_104960 _104961 : Type'} (f : type686 _104961) (a : prod _104960 _104961) (s : _104960 -> Prop) : (term104 _104960 _104961 f s a) = (term86 _104960 _104961 f a s).
Proof. exact (eq_refl (term104 _104960 _104961 f s a)). Qed.
Lemma lem4373747 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) : (@SETSPEC (prod _104960 _104961) GEN_PVAR_56) = (@SETSPEC (prod _104960 _104961) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _104960 _104961) GEN_PVAR_56)). Qed.
Lemma lem4373748 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (a : prod _104960 _104961) (s : _104960 -> Prop) : (term105 _104960 _104961 GEN_PVAR_56 f s a) = (term88 _104960 _104961 GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem4373747 _104960 _104961 GEN_PVAR_56) (@lem4373746 _104960 _104961 f a s)). Qed.
Lemma lem4373749 {_104960 _104961 : Type'} (a : prod _104960 _104961) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4373750 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) (a : prod _104960 _104961) : (term106 _104960 _104961 GEN_PVAR_56 f s a) = (term90 _104960 _104961 GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem4373748 _104960 _104961 GEN_PVAR_56 f a s) (@lem4373749 _104960 _104961 a)). Qed.
Lemma lem4373751 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term107 _104960 _104961 GEN_PVAR_56 f s) = (term92 _104960 _104961 GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : prod _104960 _104961 => @lem4373750 _104960 _104961 GEN_PVAR_56 f s a)). Qed.
Lemma lem4373752 {_104960 _104961 : Type'} : (@ex (prod _104960 _104961)) = (@ex (prod _104960 _104961)).
Proof. exact (eq_refl (@ex (prod _104960 _104961))). Qed.
Lemma lem4373753 {_104960 _104961 : Type'} (GEN_PVAR_56 : prod _104960 _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term108 _104960 _104961 GEN_PVAR_56 f s) = (term94 _104960 _104961 GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem4373752 _104960 _104961) (@lem4373751 _104960 _104961 GEN_PVAR_56 f s)). Qed.
Lemma lem4373754 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term109 _104960 _104961 f s) = (term96 _104960 _104961 f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _104960 _104961 => @lem4373753 _104960 _104961 GEN_PVAR_56 f s)). Qed.
Lemma lem4373755 {_104960 _104961 : Type'} : (@GSPEC (prod _104960 _104961)) = (@GSPEC (prod _104960 _104961)).
Proof. exact (eq_refl (@GSPEC (prod _104960 _104961))). Qed.
Lemma lem4373756 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term110 _104960 _104961 f s) = (term97 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373755 _104960 _104961) (@lem4373754 _104960 _104961 f s)). Qed.
Lemma lem4373757 {_104960 _104961 : Type'} (p1 : _104960) (p2 : _104961) : (term98 _104960 _104961 p1 p2) = (term98 _104960 _104961 p1 p2).
Proof. exact (eq_refl (term98 _104960 _104961 p1 p2)). Qed.
Lemma lem4373758 {_104960 _104961 : Type'} (p1 : _104960) (p2 : _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term101 _104960 _104961 p1 p2 f s) = (term99 _104960 _104961 p1 p2 f s).
Proof. exact (MK_COMB (@lem4373757 _104960 _104961 p1 p2) (@lem4373756 _104960 _104961 f s)). Qed.
Lemma lem4373759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373760 {_104960 _104961 : Type'} (p1 : _104960) (p2 : _104961) (f : type686 _104961) (s : _104960 -> Prop) : (term111 _104960 _104961 p1 p2 f s) = (term112 _104960 _104961 p1 p2 f s).
Proof. exact (MK_COMB (@lem4373759) (@lem4373758 _104960 _104961 p1 p2 f s)). Qed.
Lemma lem4373761 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (p2 : _104961) (s : _104960 -> Prop) : (term102 _104960 _104961 f s p1 p2) = (term113 _104960 _104961 f p1 p2 s).
Proof. exact (eq_refl (term102 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4373762 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (p2 : _104961) (s : _104960 -> Prop) : ((term101 _104960 _104961 p1 p2 f s) = (term102 _104960 _104961 f s p1 p2)) = ((term99 _104960 _104961 p1 p2 f s) = (term113 _104960 _104961 f p1 p2 s)).
Proof. exact (MK_COMB (@lem4373760 _104960 _104961 p1 p2 f s) (@lem4373761 _104960 _104961 f p1 p2 s)). Qed.
Lemma lem4373763 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (p2 : _104961) (s : _104960 -> Prop) : (term99 _104960 _104961 p1 p2 f s) = (term113 _104960 _104961 f p1 p2 s).
Proof. exact (EQ_MP (@lem4373762 _104960 _104961 f p1 p2 s) (@lem4373745 _104960 _104961 f s p1 p2)). Qed.
Lemma lem4373773 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373549 _103718 _103721 x s y t) (@lem4373548 _103718 _103721 x s y t)). Qed.
Lemma lem4373774 {_104960 _104961 : Type'} (x : _104960) (s : _104960 -> Prop) (y : _104961) (t : _104961 -> Prop) : (term7 _104960 _104961 x y s t) = (term8 _104960 _104961 x s y t).
Proof. exact (@lem4373773 _104960 _104961 x s y t). Qed.
Lemma lem4373775 {_104960 _104961 : Type'} (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (t : _104961 -> Prop) : (term7 _104960 _104961 p1 p2 s t) = (term8 _104960 _104961 p1 s p2 t).
Proof. exact (@lem4373774 _104960 _104961 p1 s p2 t). Qed.
Lemma lem4373778 {_104961 : Type'} (t : _104961 -> Prop) (f : type686 _104961) : (term78 _104961 t f) = (term78 _104961 t f).
Proof. exact (eq_refl (term78 _104961 t f)). Qed.
Lemma lem4373779 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) (t : _104961 -> Prop) : (term114 _104960 _104961 f p1 p2 s t) = (term115 _104960 _104961 f p1 s p2 t).
Proof. exact (MK_COMB (@lem4373778 _104961 t f) (@lem4373775 _104960 _104961 p1 s p2 t)). Qed.
Lemma lem4373782 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) : (term116 _104960 _104961 f p1 p2 s) = (term117 _104960 _104961 f p1 s p2).
Proof. exact (fun_ext (fun t : _104961 -> Prop => @lem4373779 _104960 _104961 f p1 s p2 t)). Qed.
Lemma lem4373783 {_104961 : Type'} : (@all (_104961 -> Prop)) = (@all (_104961 -> Prop)).
Proof. exact (eq_refl (@all (_104961 -> Prop))). Qed.
Lemma lem4373784 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) : (term113 _104960 _104961 f p1 p2 s) = (term118 _104960 _104961 f p1 s p2).
Proof. exact (MK_COMB (@lem4373783 _104961) (@lem4373782 _104960 _104961 f p1 s p2)). Qed.
Lemma lem4373791 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) : (term99 _104960 _104961 p1 p2 f s) = (term118 _104960 _104961 f p1 s p2).
Proof. exact (TRANS (@lem4373763 _104960 _104961 f p1 p2 s) (@lem4373784 _104960 _104961 f p1 s p2)). Qed.
Lemma lem4373792 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) : (term44 _104960 _104961 p1 p2 f s) = (term118 _104960 _104961 f p1 s p2).
Proof. exact (TRANS (@lem4373741 _104960 _104961 p1 p2 f s) (@lem4373791 _104960 _104961 f p1 s p2)). Qed.
Lemma lem4373793 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) (p2 : _104961) : ((term43 _104960 _104961 p1 p2 s f) = (term44 _104960 _104961 p1 p2 f s)) = ((term52 _104960 _104961 p1 s p2 f) = (term118 _104960 _104961 f p1 s p2)).
Proof. exact (MK_COMB (@lem4373686 _104960 _104961 p1 s p2 f) (@lem4373792 _104960 _104961 f p1 s p2)). Qed.
Lemma lem4373798 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) : (term46 _104960 _104961 p1 f s) = (term119 _104960 _104961 f p1 s).
Proof. exact (fun_ext (fun p2 : _104961 => @lem4373793 _104960 _104961 f p1 s p2)). Qed.
Lemma lem4373799 {_104961 : Type'} : (@all _104961) = (@all _104961).
Proof. exact (eq_refl (@all _104961)). Qed.
Lemma lem4373800 {_104960 _104961 : Type'} (f : type686 _104961) (p1 : _104960) (s : _104960 -> Prop) : (term48 _104960 _104961 p1 f s) = (term120 _104960 _104961 f p1 s).
Proof. exact (MK_COMB (@lem4373799 _104961) (@lem4373798 _104960 _104961 f p1 s)). Qed.
Lemma lem4373807 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term50 _104960 _104961 f s) = (term121 _104960 _104961 f s).
Proof. exact (fun_ext (fun p1 : _104960 => @lem4373800 _104960 _104961 f p1 s)). Qed.
Lemma lem4373808 {_104960 : Type'} : (@all _104960) = (@all _104960).
Proof. exact (eq_refl (@all _104960)). Qed.
Lemma lem4373809 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term51 _104960 _104961 f s) = (term122 _104960 _104961 f s).
Proof. exact (MK_COMB (@lem4373808 _104960) (@lem4373807 _104960 _104961 f s)). Qed.
Lemma lem4373816 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : ((term28 _104960 _104961 s f) = (term29 _104960 _104961 f s)) = (term122 _104960 _104961 f s).
Proof. exact (TRANS (@lem4373668 _104960 _104961 f s) (@lem4373809 _104960 _104961 f s)). Qed.
Lemma lem4373817 {_104960 _104961 : Type'} (f : type686 _104961) (s : _104960 -> Prop) : (term122 _104960 _104961 f s) = ((term28 _104960 _104961 s f) = (term29 _104960 _104961 f s)).
Proof. exact (SYM (@lem4373816 _104960 _104961 f s)). Qed.
