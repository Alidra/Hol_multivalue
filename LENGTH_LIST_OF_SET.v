Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_LIST_OF_SET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LIST_OF_SET_PROPERTIES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4787465 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4787466 {_110321 : Type'} : (term1 _110321) = (term2 _110321).
Proof. exact (@lem4787465 (term1 _110321)). Qed.
Lemma lem4787467 {_110321 : Type'} : (term2 _110321) = (term1 _110321).
Proof. exact (SYM (@lem4787466 _110321)). Qed.
Lemma lem4787468 {_110321 : Type'} (h1 : term3 _110321) : term3 _110321.
Proof. exact (h1). Qed.
Lemma lem4787469 {_110321 : Type'} : term4 _110321.
Proof. exact (@lem4786967 _110321). Qed.
Lemma lem4787475 {_110321 A : Type'} (h1 : term5 _110321 A) : term5 _110321 A.
Proof. exact (h1). Qed.
Lemma lem4787476 {_110321 A : Type'} : term6 _110321 A.
Proof. exact (fun h0 : term5 _110321 A => @lem4787475 _110321 A h0). Qed.
Lemma lem4787477 {_110321 A : Type'} (h1 : term6 _110321 A) : term6 _110321 A.
Proof. exact (h1). Qed.
Lemma lem4787478 {_110321 A : Type'} (h1 : term5 _110321 A) : term5 _110321 A.
Proof. exact (h1). Qed.
Lemma lem4787479 {_110321 A : Type'} (h1 : term5 _110321 A) (h2 : term6 _110321 A) : term5 _110321 A.
Proof. exact (@lem4787477 _110321 A h2 (@lem4787478 _110321 A h1)). Qed.
Lemma lem4787480 {_110321 A : Type'} (h1 : term5 _110321 A) : term7 _110321 A.
Proof. exact (fun h0 : term6 _110321 A => @lem4787479 _110321 A h1 h0). Qed.
Lemma lem4787481 {_110321 A : Type'} (h1 : term6 _110321 A) : term6 _110321 A.
Proof. exact (h1). Qed.
Lemma lem4787482 {_110321 A : Type'} (h1 : term5 _110321 A) (h2 : term6 _110321 A) : term5 _110321 A.
Proof. exact (@lem4787480 _110321 A h1 (@lem4787481 _110321 A h2)). Qed.
Lemma lem4787483 {_110321 A : Type'} (h1 : term6 _110321 A) : term6 _110321 A.
Proof. exact (fun h0 : term5 _110321 A => @lem4787482 _110321 A h0 h1). Qed.
Lemma lem4787484 {_110321 A : Type'} : term8 _110321 A.
Proof. exact (fun h0 : term6 _110321 A => @lem4787483 _110321 A h0). Qed.
Lemma lem4787487 {_110321 A : Type'} : term6 _110321 A.
Proof. exact (@lem4787484 _110321 A (@lem4787476 _110321 A)). Qed.
Lemma lem4787488 {_110321 A : Type'} : term6 _110321 A.
Proof. exact (@lem4787487 _110321 A). Qed.
Lemma lem4787508 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4787509 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem4787508 (term4 A)). Qed.
Lemma lem4787518 {_110321 : Type'} : (term11 _110321) = (term11 _110321).
Proof. exact (eq_refl (term11 _110321)). Qed.
Lemma lem4787519 {_110321 A : Type'} : (term12 _110321 A) = (term13 _110321 A).
Proof. exact (MK_COMB (@lem4787518 _110321) (@lem4787509 A)). Qed.
Lemma lem4787522 {_110321 : Type'} : (term14 _110321) = (term14 _110321).
Proof. exact (eq_refl (term14 _110321)). Qed.
Lemma lem4787529 {_110321 A : Type'} : (term5 _110321 A) = (term15 _110321 A).
Proof. exact (MK_COMB (@lem4787522 _110321) (@lem4787519 _110321 A)). Qed.
Lemma lem4787538 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4787539 {A : Type'} : (term17 A) = (term17 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4787538 A s)). Qed.
Lemma lem4787540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4787541 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem4787540 A) (@lem4787539 A)). Qed.
Lemma lem4787542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4787543 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem4787542) (@lem4787541 A)). Qed.
Lemma lem4787552 {_110321 : Type'} (s : _110321 -> Prop) : (term16 _110321 s) = (term16 _110321 s).
Proof. exact (eq_refl (term16 _110321 s)). Qed.
Lemma lem4787553 {_110321 : Type'} : (term17 _110321) = (term17 _110321).
Proof. exact (fun_ext (fun s : _110321 -> Prop => @lem4787552 _110321 s)). Qed.
Lemma lem4787554 {_110321 : Type'} : (@all (_110321 -> Prop)) = (@all (_110321 -> Prop)).
Proof. exact (eq_refl (@all (_110321 -> Prop))). Qed.
Lemma lem4787555 {_110321 : Type'} : (term4 _110321) = (term4 _110321).
Proof. exact (MK_COMB (@lem4787554 _110321) (@lem4787553 _110321)). Qed.
Lemma lem4787556 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4787557 {_110321 : Type'} : (term11 _110321) = (term11 _110321).
Proof. exact (MK_COMB (@lem4787556) (@lem4787555 _110321)). Qed.
Lemma lem4787558 {_110321 A : Type'} : (term13 _110321 A) = (term13 _110321 A).
Proof. exact (MK_COMB (@lem4787557 _110321) (@lem4787543 A)). Qed.
Lemma lem4787563 {_110321 : Type'} (s : _110321 -> Prop) : (term18 _110321 s) = (term18 _110321 s).
Proof. exact (eq_refl (term18 _110321 s)). Qed.
Lemma lem4787564 {_110321 : Type'} : (term19 _110321) = (term19 _110321).
Proof. exact (fun_ext (fun s : _110321 -> Prop => @lem4787563 _110321 s)). Qed.
Lemma lem4787565 {_110321 : Type'} : (@all (_110321 -> Prop)) = (@all (_110321 -> Prop)).
Proof. exact (eq_refl (@all (_110321 -> Prop))). Qed.
Lemma lem4787566 {_110321 : Type'} : (term1 _110321) = (term1 _110321).
Proof. exact (MK_COMB (@lem4787565 _110321) (@lem4787564 _110321)). Qed.
Lemma lem4787567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4787568 {_110321 : Type'} : (term3 _110321) = (term3 _110321).
Proof. exact (MK_COMB (@lem4787567) (@lem4787566 _110321)). Qed.
Lemma lem4787569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4787570 {_110321 : Type'} : (term14 _110321) = (term14 _110321).
Proof. exact (MK_COMB (@lem4787569) (@lem4787568 _110321)). Qed.
Lemma lem4787571 {_110321 A : Type'} : (term15 _110321 A) = (term15 _110321 A).
Proof. exact (MK_COMB (@lem4787570 _110321) (@lem4787558 _110321 A)). Qed.
Lemma lem4787606 {_110321 A : Type'} : (term5 _110321 A) = (term15 _110321 A).
Proof. exact (TRANS (@lem4787529 _110321 A) (@lem4787571 _110321 A)). Qed.
Lemma lem4787607 {_110321 A : Type'} : (term15 _110321 A) = (term5 _110321 A).
Proof. exact (SYM (@lem4787606 _110321 A)). Qed.
Lemma lem4787608 {_110321 : Type'} (h1 : term3 _110321) : term3 _110321.
Proof. exact (h1). Qed.
Lemma lem4787609 {_110321 : Type'} (h1 : term4 _110321) : term4 _110321.
Proof. exact (h1). Qed.
Lemma lem4787617 {_110321 : Type'} (s : _110321 -> Prop) : (term20 _110321 s) = (term21 _110321 s).
Proof. exact (@lem17362 (@FINITE _110321 s) ((term22 _110321 s) = (@CARD _110321 s))). Qed.
Lemma lem4787618 {_110321 : Type'} (P : type686 _110321) : (term23 _110321 P) = (term24 _110321 P).
Proof. exact (@lem18392 (_110321 -> Prop) P). Qed.
Lemma lem4787619 {_110321 : Type'} : (term3 _110321) = (term25 _110321).
Proof. exact (@lem4787618 _110321 (term19 _110321)). Qed.
Lemma lem4787620 {_110321 : Type'} (s : _110321 -> Prop) : (term26 _110321 s) = (term18 _110321 s).
Proof. exact (eq_refl (term26 _110321 s)). Qed.
Lemma lem4787621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4787622 {_110321 : Type'} (s : _110321 -> Prop) : (term27 _110321 s) = (term20 _110321 s).
Proof. exact (MK_COMB (@lem4787621) (@lem4787620 _110321 s)). Qed.
Lemma lem4787623 {_110321 : Type'} (s : _110321 -> Prop) : (term27 _110321 s) = (term21 _110321 s).
Proof. exact (TRANS (@lem4787622 _110321 s) (@lem4787617 _110321 s)). Qed.
Lemma lem4787624 {_110321 : Type'} : (term28 _110321) = (term29 _110321).
Proof. exact (fun_ext (fun s : _110321 -> Prop => @lem4787623 _110321 s)). Qed.
Lemma lem4787625 {_110321 : Type'} : (@ex (_110321 -> Prop)) = (@ex (_110321 -> Prop)).
Proof. exact (eq_refl (@ex (_110321 -> Prop))). Qed.
Lemma lem4787626 {_110321 : Type'} : (term25 _110321) = (term30 _110321).
Proof. exact (MK_COMB (@lem4787625 _110321) (@lem4787624 _110321)). Qed.
Lemma lem4787659 {_110321 : Type'} : (term3 _110321) = (term30 _110321).
Proof. exact (TRANS (@lem4787619 _110321) (@lem4787626 _110321)). Qed.
Lemma lem4787660 {_110321 : Type'} (h1 : term3 _110321) : term30 _110321.
Proof. exact (EQ_MP (@lem4787659 _110321) (@lem4787608 _110321 h1)). Qed.
Lemma lem4787671 {_110321 : Type'} (s : _110321 -> Prop) : (term16 _110321 s) = (term31 _110321 s).
Proof. exact (@lem17265 (@FINITE _110321 s) (term32 _110321 s)). Qed.
Lemma lem4787672 {_110321 : Type'} : (term17 _110321) = (term33 _110321).
Proof. exact (fun_ext (fun s : _110321 -> Prop => @lem4787671 _110321 s)). Qed.
Lemma lem4787673 {_110321 : Type'} : (@all (_110321 -> Prop)) = (@all (_110321 -> Prop)).
Proof. exact (eq_refl (@all (_110321 -> Prop))). Qed.
Lemma lem4787726 {_110321 : Type'} : (term4 _110321) = (term34 _110321).
Proof. exact (MK_COMB (@lem4787673 _110321) (@lem4787672 _110321)). Qed.
Lemma lem4787727 {_110321 : Type'} (h1 : term4 _110321) : term34 _110321.
Proof. exact (EQ_MP (@lem4787726 _110321) (@lem4787609 _110321 h1)). Qed.
Lemma lem4787826 {_110321 : Type'} (s : _110321 -> Prop) : (term31 _110321 s) = (term31 _110321 s).
Proof. exact (eq_refl (term31 _110321 s)). Qed.
Lemma lem4787827 {_110321 : Type'} : (term33 _110321) = (term33 _110321).
Proof. exact (fun_ext (fun s : _110321 -> Prop => @lem4787826 _110321 s)). Qed.
Lemma lem4787828 {_110321 : Type'} : (@all (_110321 -> Prop)) = (@all (_110321 -> Prop)).
Proof. exact (eq_refl (@all (_110321 -> Prop))). Qed.
Lemma lem4787829 {_110321 : Type'} : (term34 _110321) = (term34 _110321).
Proof. exact (MK_COMB (@lem4787828 _110321) (@lem4787827 _110321)). Qed.
Lemma lem4787830 {_110321 : Type'} (h1 : term4 _110321) : term34 _110321.
Proof. exact (EQ_MP (@lem4787829 _110321) (@lem4787727 _110321 h1)). Qed.
Lemma lem4787885 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term21 _110321 s) : term21 _110321 s.
Proof. exact (h1). Qed.
Lemma lem4787905 {_110321 : Type'} (s : _110321 -> Prop) : (term31 _110321 s) = (term35 _110321 s).
Proof. exact (@lem19490 ((term36 _110321 s) = s) (term37 _110321 s) ((term22 _110321 s) = (@CARD _110321 s))). Qed.
Lemma lem4787906 {_110321 : Type'} : (term33 _110321) = (term38 _110321).
Proof. exact (fun_ext (fun s : _110321 -> Prop => @lem4787905 _110321 s)). Qed.
Lemma lem4787907 {_110321 : Type'} : (@all (_110321 -> Prop)) = (@all (_110321 -> Prop)).
Proof. exact (eq_refl (@all (_110321 -> Prop))). Qed.
Lemma lem4787909 {_110321 : Type'} : (term34 _110321) = (term39 _110321).
Proof. exact (MK_COMB (@lem4787907 _110321) (@lem4787906 _110321)). Qed.
Lemma lem4787910 {_110321 : Type'} (h1 : term4 _110321) : term39 _110321.
Proof. exact (EQ_MP (@lem4787909 _110321) (@lem4787830 _110321 h1)). Qed.
Lemma lem4787942 {_110321 : Type'} (_59134 : _110321 -> Prop) (h1 : term4 _110321) : term40 _110321 _59134.
Proof. exact (@lem4787910 _110321 h1 _59134). Qed.
Lemma lem4787943 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term40 _110321 _59134) = (term35 _110321 _59134).
Proof. exact (eq_refl (term40 _110321 _59134)). Qed.
Lemma lem4787944 {_110321 : Type'} (_59134 : _110321 -> Prop) (h1 : term4 _110321) : term35 _110321 _59134.
Proof. exact (EQ_MP (@lem4787943 _110321 _59134) (@lem4787942 _110321 _59134 h1)). Qed.
Lemma lem4787955 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term21 _110321 s) : term41 _110321 s.
Proof. exact (proj2 (@lem4787885 _110321 s h1)). Qed.
Lemma lem4787979 {_110321 : Type'} (_59134 : _110321 -> Prop) (h1 : term4 _110321) : term42 _110321 _59134.
Proof. exact (proj2 (@lem4787944 _110321 _59134 h1)). Qed.
Lemma lem4788079 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term21 _110321 s) : @FINITE _110321 s.
Proof. exact (proj1 (@lem4787885 _110321 s h1)). Qed.
Lemma lem4788080 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term21 _110321 s) : term43 _110321 s.
Proof. exact (fun h0 : term37 _110321 s => @lem4788079 _110321 s h1). Qed.
Lemma lem4788082 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4788083 {_110321 : Type'} (s : _110321 -> Prop) : (term43 _110321 s) = (@FINITE _110321 s).
Proof. exact (@lem4788082 (@FINITE _110321 s)). Qed.
Lemma lem4788084 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term21 _110321 s) : @FINITE _110321 s.
Proof. exact (EQ_MP (@lem4788083 _110321 s) (@lem4788080 _110321 s h1)). Qed.
Lemma lem4788090 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4788091 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term42 _110321 _59134) = (term45 _110321 _59134).
Proof. exact (@lem4788090 ((term22 _110321 _59134) = (@CARD _110321 _59134)) (term37 _110321 _59134)). Qed.
Lemma lem4788099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4788100 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term46 _110321 _59134) = (term47 _110321 _59134).
Proof. exact (MK_COMB (@lem4788099) (@lem4788091 _110321 _59134)). Qed.
Lemma lem4788108 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term45 _110321 _59134) = (term45 _110321 _59134).
Proof. exact (eq_refl (term45 _110321 _59134)). Qed.
Lemma lem4788109 {_110321 : Type'} (_59134 : _110321 -> Prop) : ((term42 _110321 _59134) = (term45 _110321 _59134)) = ((term45 _110321 _59134) = (term45 _110321 _59134)).
Proof. exact (MK_COMB (@lem4788100 _110321 _59134) (@lem4788108 _110321 _59134)). Qed.
Lemma lem4788111 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4788112 (x : Prop) : (x = x) = True.
Proof. exact (@lem4788111 Prop x). Qed.
Lemma lem4788113 {_110321 : Type'} (_59134 : _110321 -> Prop) : ((term45 _110321 _59134) = (term45 _110321 _59134)) = True.
Proof. exact (@lem4788112 (term45 _110321 _59134)). Qed.
Lemma lem4788114 {_110321 : Type'} (_59134 : _110321 -> Prop) : ((term42 _110321 _59134) = (term45 _110321 _59134)) = True.
Proof. exact (TRANS (@lem4788109 _110321 _59134) (@lem4788113 _110321 _59134)). Qed.
Lemma lem4788115 {_110321 : Type'} (_59134 : _110321 -> Prop) : True = ((term42 _110321 _59134) = (term45 _110321 _59134)).
Proof. exact (SYM (@lem4788114 _110321 _59134)). Qed.
Lemma lem4788116 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term42 _110321 _59134) = (term45 _110321 _59134).
Proof. exact (EQ_MP (@lem4788115 _110321 _59134) (@lem0)). Qed.
Lemma lem4788117 {_110321 : Type'} (_59134 : _110321 -> Prop) (h1 : term4 _110321) : term45 _110321 _59134.
Proof. exact (EQ_MP (@lem4788116 _110321 _59134) (@lem4787979 _110321 _59134 h1)). Qed.
Lemma lem4788119 (b : Prop) (a : Prop) : (a \/ b) = (term48 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4788120 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term45 _110321 _59134) = (term49 _110321 _59134).
Proof. exact (@lem4788119 (term37 _110321 _59134) ((term22 _110321 _59134) = (@CARD _110321 _59134))). Qed.
Lemma lem4788122 (a : Prop) : (term50 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4788123 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term51 _110321 _59134) = (@FINITE _110321 _59134).
Proof. exact (@lem4788122 (@FINITE _110321 _59134)). Qed.
Lemma lem4788124 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4788125 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term52 _110321 _59134) = (term53 _110321 _59134).
Proof. exact (MK_COMB (@lem4788124) (@lem4788123 _110321 _59134)). Qed.
Lemma lem4788126 {_110321 : Type'} (_59134 : _110321 -> Prop) : ((term22 _110321 _59134) = (@CARD _110321 _59134)) = ((term22 _110321 _59134) = (@CARD _110321 _59134)).
Proof. exact (eq_refl ((term22 _110321 _59134) = (@CARD _110321 _59134))). Qed.
Lemma lem4788127 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term49 _110321 _59134) = (term18 _110321 _59134).
Proof. exact (MK_COMB (@lem4788125 _110321 _59134) (@lem4788126 _110321 _59134)). Qed.
Lemma lem4788128 {_110321 : Type'} (_59134 : _110321 -> Prop) : (term45 _110321 _59134) = (term18 _110321 _59134).
Proof. exact (TRANS (@lem4788120 _110321 _59134) (@lem4788127 _110321 _59134)). Qed.
Lemma lem4788131 {_110321 : Type'} (_59134 : _110321 -> Prop) (h1 : term4 _110321) : term18 _110321 _59134.
Proof. exact (EQ_MP (@lem4788128 _110321 _59134) (@lem4788117 _110321 _59134 h1)). Qed.
Lemma lem4788132 {_110321 : Type'} (_59134 : _110321 -> Prop) (h1 : term4 _110321) : term18 _110321 _59134.
Proof. exact (@lem4788131 _110321 _59134 h1). Qed.
Lemma lem4788133 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) : term18 _110321 s.
Proof. exact (@lem4788132 _110321 s h1). Qed.
Lemma lem4788136 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : (term22 _110321 s) = (@CARD _110321 s).
Proof. exact (@lem4788133 _110321 s h1 (@lem4788084 _110321 s h2)). Qed.
Lemma lem4788137 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : term54 _110321 s.
Proof. exact (fun h0 : term41 _110321 s => @lem4788136 _110321 s h1 h2). Qed.
Lemma lem4788139 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4788140 {_110321 : Type'} (s : _110321 -> Prop) : (term54 _110321 s) = ((term22 _110321 s) = (@CARD _110321 s)).
Proof. exact (@lem4788139 ((term22 _110321 s) = (@CARD _110321 s))). Qed.
Lemma lem4788141 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : (term22 _110321 s) = (@CARD _110321 s).
Proof. exact (EQ_MP (@lem4788140 _110321 s) (@lem4788137 _110321 s h1 h2)). Qed.
Lemma lem4788144 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4788146 {_110321 : Type'} (s : _110321 -> Prop) : (term41 _110321 s) = (term55 _110321 s).
Proof. exact (@lem4788144 ((term22 _110321 s) = (@CARD _110321 s))). Qed.
Lemma lem4788149 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term21 _110321 s) : term55 _110321 s.
Proof. exact (EQ_MP (@lem4788146 _110321 s) (@lem4787955 _110321 s h1)). Qed.
Lemma lem4788152 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : False.
Proof. exact (@lem4788149 _110321 s h2 (@lem4788141 _110321 s h1 h2)). Qed.
Lemma lem4788153 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : term56.
Proof. exact (fun h0 : ~ False => @lem4788152 _110321 s h1 h2). Qed.
Lemma lem4788155 (p : Prop) : (term44 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4788156 : term56 = False.
Proof. exact (@lem4788155 False). Qed.
Lemma lem4788157 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : False.
Proof. exact (EQ_MP (@lem4788156) (@lem4788153 _110321 s h1 h2)). Qed.
Lemma lem4788158 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : (term21 _110321 s) = False.
Proof. exact (prop_ext (fun h3 : term21 _110321 s => @lem4788157 _110321 s h1 h2) (fun h3 : False => @lem4787885 _110321 s h2)). Qed.
Lemma lem4788159 {_110321 : Type'} (s : _110321 -> Prop) (h1 : term4 _110321) (h2 : term21 _110321 s) : False.
Proof. exact (EQ_MP (@lem4788158 _110321 s h1 h2) (@lem4787885 _110321 s h2)). Qed.
Lemma lem4788160 {_110321 : Type'} (h1 : term4 _110321) (h2 : term3 _110321) : False.
Proof. exact (ex_elim (@lem4787660 _110321 h2) (fun s : _110321 -> Prop => fun h0 : term29 _110321 s => @lem4788159 _110321 s h1 h0)). Qed.
Lemma lem4788161 {_110321 A : Type'} (h1 : term4 _110321) (h2 : term3 _110321) : term9 A.
Proof. exact (fun h0 : term4 A => @lem4788160 _110321 h1 h2). Qed.
Lemma lem4788162 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem4788163 {_110321 A : Type'} (h1 : term4 _110321) (h2 : term3 _110321) : term10 A.
Proof. exact (EQ_MP (@lem4788162 A) (@lem4788161 _110321 A h1 h2)). Qed.
Lemma lem4788164 {_110321 A : Type'} (h1 : term3 _110321) : term13 _110321 A.
Proof. exact (fun h0 : term4 _110321 => @lem4788163 _110321 A h0 h1). Qed.
Lemma lem4788165 {_110321 A : Type'} : term15 _110321 A.
Proof. exact (fun h0 : term3 _110321 => @lem4788164 _110321 A h0). Qed.
Lemma lem4788166 {_110321 A : Type'} : term5 _110321 A.
Proof. exact (EQ_MP (@lem4787607 _110321 A) (@lem4788165 _110321 A)). Qed.
Lemma lem4788168 {_110321 A : Type'} : term5 _110321 A.
Proof. exact (@lem4787488 _110321 A (@lem4788166 _110321 A)). Qed.
Lemma lem4788169 {_110321 A : Type'} (h1 : term3 _110321) : term12 _110321 A.
Proof. exact (@lem4788168 _110321 A (@lem4787468 _110321 h1)). Qed.
Lemma lem4788170 {_110321 A : Type'} (h1 : term3 _110321) : term9 A.
Proof. exact (@lem4788169 _110321 A h1 (@lem4787469 _110321)). Qed.
Lemma lem4788171 {_110321 : Type'} (h1 : term3 _110321) : False.
Proof. exact (@lem4788170 _110321 Prop h1 (@lem4786967 Prop)). Qed.
Lemma lem4788172 {_110321 : Type'} (h1 : term3 _110321) : (term3 _110321) = False.
Proof. exact (prop_ext (fun h2 : term3 _110321 => @lem4788171 _110321 h1) (fun h2 : False => @lem4787468 _110321 h1)). Qed.
Lemma lem4788173 {_110321 : Type'} (h1 : term3 _110321) : False.
Proof. exact (EQ_MP (@lem4788172 _110321 h1) (@lem4787468 _110321 h1)). Qed.
Lemma lem4788174 {_110321 : Type'} : term2 _110321.
Proof. exact (fun h0 : term3 _110321 => @lem4788173 _110321 h0). Qed.
Lemma lem4788175 {_110321 : Type'} : term1 _110321.
Proof. exact (EQ_MP (@lem4787467 _110321) (@lem4788174 _110321)). Qed.
