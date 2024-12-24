Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_CARTESIAN_PRODUCT_ELEMENT_term_abbrevs.
Require Import CARTESIAN_PRODUCT_AS_RESTRICTIONS_spec.
Require Import DISJ_ACI_spec.
Require Import EXISTS_IN_GSPEC_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4452637 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4452638 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4452639 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4452638 A B s) (@lem4452637 A B s)). Qed.
Lemma lem4452640 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4452639 A B s f). Qed.
Lemma lem4452641 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4452642 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4452641 A B s f) (@lem4452640 A B s f)). Qed.
Lemma lem4452643 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4452642 A B s f x). Qed.
Lemma lem4452644 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4452669 {_89156 _89357 : Type'} (Q : _89357 -> Prop) : term6 _89156 _89357 Q.
Proof. exact (proj1 (@lem3449335 _89156 Prop Prop Prop Prop Prop _89357 Prop Prop Prop Prop Q)). Qed.
Lemma lem4452670 {_89156 _89357 : Type'} (Q : _89357 -> Prop) (P : _89156 -> Prop) : term7 _89156 _89357 Q P.
Proof. exact (@lem4452669 _89156 _89357 Q P). Qed.
Lemma lem4452671 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) : (term7 _89156 _89357 Q P) = (term8 _89156 _89357 P Q).
Proof. exact (eq_refl (term7 _89156 _89357 Q P)). Qed.
Lemma lem4452672 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) : term8 _89156 _89357 P Q.
Proof. exact (EQ_MP (@lem4452671 _89156 _89357 P Q) (@lem4452670 _89156 _89357 Q P)). Qed.
Lemma lem4452673 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : term9 _89156 _89357 P Q f.
Proof. exact (@lem4452672 _89156 _89357 P Q f). Qed.
Lemma lem4452674 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : (term9 _89156 _89357 P Q f) = ((term10 _89156 _89357 P f Q) = (term11 _89156 _89357 P Q f)).
Proof. exact (eq_refl (term9 _89156 _89357 P Q f)). Qed.
Lemma lem4452676 {A K : Type'} (k : K -> Prop) : term12 A K k.
Proof. exact (@lem4406347 A K k). Qed.
Lemma lem4452677 {A K : Type'} (k : K -> Prop) : (term12 A K k) = (term13 A K k).
Proof. exact (eq_refl (term12 A K k)). Qed.
Lemma lem4452678 {A K : Type'} (k : K -> Prop) : term13 A K k.
Proof. exact (EQ_MP (@lem4452677 A K k) (@lem4452676 A K k)). Qed.
Lemma lem4452679 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term14 A K k s.
Proof. exact (@lem4452678 A K k s). Qed.
Lemma lem4452680 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term14 A K k s) = ((@cartesian_product A K k s) = (term15 A K s k)).
Proof. exact (eq_refl (term14 A K k s)). Qed.
Lemma lem4452691 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (@cartesian_product A K k s) = (term15 A K s k).
Proof. exact (EQ_MP (@lem4452680 A K s k) (@lem4452679 A K k s)). Qed.
Lemma lem4452692 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (@cartesian_product A K k s) = (term15 A K s k).
Proof. exact (@lem4452691 A K s k). Qed.
Lemma lem4452703 {A K : Type'} (z : K -> A) : (@IN (K -> A) z) = (@IN (K -> A) z).
Proof. exact (eq_refl (@IN (K -> A) z)). Qed.
Lemma lem4452704 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) : (term16 A K z k s) = (term17 A K z s k).
Proof. exact (MK_COMB (@lem4452703 A K z) (@lem4452692 A K s k)). Qed.
Lemma lem4452705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4452706 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) : (term18 A K z k s) = (term19 A K z s k).
Proof. exact (MK_COMB (@lem4452705) (@lem4452704 A K z s k)). Qed.
Lemma lem4452713 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term20 A K k P z) = (term20 A K k P z).
Proof. exact (eq_refl (term20 A K k P z)). Qed.
Lemma lem4452714 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term21 A K s k P z) = (term22 A K s k P z).
Proof. exact (MK_COMB (@lem4452706 A K z s k) (@lem4452713 A K k P z)). Qed.
Lemma lem4452717 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term23 A K s k P) = (term24 A K s k P).
Proof. exact (fun_ext (fun z : K -> A => @lem4452714 A K s k P z)). Qed.
Lemma lem4452718 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4452719 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term25 A K s k P) = (term26 A K s k P).
Proof. exact (MK_COMB (@lem4452718 A K) (@lem4452717 A K s k P)). Qed.
Lemma lem4452721 {_89156 _89357 : Type'} (P : _89156 -> Prop) (Q : _89357 -> Prop) (f : _89156 -> _89357) : (term10 _89156 _89357 P f Q) = (term11 _89156 _89357 P Q f).
Proof. exact (EQ_MP (@lem4452674 _89156 _89357 P Q f) (@lem4452673 _89156 _89357 P Q f)). Qed.
Lemma lem4452722 {A K : Type'} (P : type805 A K) (Q : type805 A K) (f : type796 A K) : (term27 A K P f Q) = (term28 A K P Q f).
Proof. exact (@lem4452721 (K -> A) (K -> A) P Q f). Qed.
Lemma lem4452723 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term29 A K s k P) = (term30 A K s P k).
Proof. exact (@lem4452722 A K (term31 A K k s) (term32 A K k P) (term33 A K k)). Qed.
Lemma lem4452724 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term34 A K k s f) = (term35 A K k f s).
Proof. exact (eq_refl (term34 A K k s f)). Qed.
Lemma lem4452725 {A K : Type'} (GEN_PVAR_142 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_142) = (@SETSPEC (K -> A) GEN_PVAR_142).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_142)). Qed.
Lemma lem4452726 {A K : Type'} (GEN_PVAR_142 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term36 A K GEN_PVAR_142 k s f) = (term37 A K GEN_PVAR_142 k f s).
Proof. exact (MK_COMB (@lem4452725 A K GEN_PVAR_142) (@lem4452724 A K k f s)). Qed.
Lemma lem4452727 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term38 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term38 A K k f)). Qed.
Lemma lem4452728 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term39 A K GEN_PVAR_142 s k f) = (term40 A K GEN_PVAR_142 s k f).
Proof. exact (MK_COMB (@lem4452726 A K GEN_PVAR_142 k f s) (@lem4452727 A K k f)). Qed.
Lemma lem4452729 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) : (term41 A K GEN_PVAR_142 s k) = (term42 A K GEN_PVAR_142 s k).
Proof. exact (fun_ext (fun f : K -> A => @lem4452728 A K GEN_PVAR_142 s k f)). Qed.
Lemma lem4452730 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4452731 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) : (term43 A K GEN_PVAR_142 s k) = (term44 A K GEN_PVAR_142 s k).
Proof. exact (MK_COMB (@lem4452730 A K) (@lem4452729 A K GEN_PVAR_142 s k)). Qed.
Lemma lem4452732 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term45 A K s k) = (term46 A K s k).
Proof. exact (fun_ext (fun GEN_PVAR_142 : K -> A => @lem4452731 A K GEN_PVAR_142 s k)). Qed.
Lemma lem4452733 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4452734 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term47 A K s k) = (term15 A K s k).
Proof. exact (MK_COMB (@lem4452733 A K) (@lem4452732 A K s k)). Qed.
Lemma lem4452735 {A K : Type'} (z : K -> A) : (@IN (K -> A) z) = (@IN (K -> A) z).
Proof. exact (eq_refl (@IN (K -> A) z)). Qed.
Lemma lem4452736 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) : (term48 A K z s k) = (term17 A K z s k).
Proof. exact (MK_COMB (@lem4452735 A K z) (@lem4452734 A K s k)). Qed.
Lemma lem4452737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4452738 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) : (term49 A K z s k) = (term19 A K z s k).
Proof. exact (MK_COMB (@lem4452737) (@lem4452736 A K z s k)). Qed.
Lemma lem4452739 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term50 A K k P z) = (term20 A K k P z).
Proof. exact (eq_refl (term50 A K k P z)). Qed.
Lemma lem4452740 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term51 A K s k P z) = (term22 A K s k P z).
Proof. exact (MK_COMB (@lem4452738 A K z s k) (@lem4452739 A K k P z)). Qed.
Lemma lem4452741 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term52 A K s k P) = (term24 A K s k P).
Proof. exact (fun_ext (fun z : K -> A => @lem4452740 A K s k P z)). Qed.
Lemma lem4452742 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4452743 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term29 A K s k P) = (term26 A K s k P).
Proof. exact (MK_COMB (@lem4452742 A K) (@lem4452741 A K s k P)). Qed.
Lemma lem4452744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4452745 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term53 A K s k P) = (term54 A K s k P).
Proof. exact (MK_COMB (@lem4452744) (@lem4452743 A K s k P)). Qed.
Lemma lem4452746 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term34 A K k s f) = (term35 A K k f s).
Proof. exact (eq_refl (term34 A K k s f)). Qed.
Lemma lem4452747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4452748 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term55 A K k s f) = (term56 A K k f s).
Proof. exact (MK_COMB (@lem4452747) (@lem4452746 A K k f s)). Qed.
Lemma lem4452749 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) : (term57 A K P k f) = (term58 A K P k f).
Proof. exact (eq_refl (term57 A K P k f)). Qed.
Lemma lem4452750 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) (f : K -> A) : (term59 A K s P k f) = (term60 A K s P k f).
Proof. exact (MK_COMB (@lem4452748 A K k f s) (@lem4452749 A K P k f)). Qed.
Lemma lem4452751 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term61 A K s P k) = (term62 A K s P k).
Proof. exact (fun_ext (fun f : K -> A => @lem4452750 A K s P k f)). Qed.
Lemma lem4452752 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4452753 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term30 A K s P k) = (term63 A K s P k).
Proof. exact (MK_COMB (@lem4452752 A K) (@lem4452751 A K s P k)). Qed.
Lemma lem4452754 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : ((term29 A K s k P) = (term30 A K s P k)) = ((term26 A K s k P) = (term63 A K s P k)).
Proof. exact (MK_COMB (@lem4452745 A K s k P) (@lem4452753 A K s P k)). Qed.
Lemma lem4452755 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term26 A K s k P) = (term63 A K s P k).
Proof. exact (EQ_MP (@lem4452754 A K s P k) (@lem4452723 A K s P k)). Qed.
Lemma lem4452775 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4452776 {A K : Type'} (f : type796 A K) (y : K -> A) : (term65 A K f y) = (f y).
Proof. exact (@lem4452775 (K -> A) (K -> A) f y). Qed.
Lemma lem4452777 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term66 A K k f) = (term38 A K k f).
Proof. exact (@lem4452776 A K (term33 A K k) f). Qed.
Lemma lem4452778 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term38 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term38 A K k f)). Qed.
Lemma lem4452779 {A K : Type'} (k : K -> Prop) : (term67 A K k) = (term33 A K k).
Proof. exact (fun_ext (fun f : K -> A => @lem4452778 A K k f)). Qed.
Lemma lem4452780 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4452781 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term66 A K k f) = (term38 A K k f).
Proof. exact (MK_COMB (@lem4452779 A K k) (@lem4452780 A K f)). Qed.
Lemma lem4452782 {A K : Type'} : (@eq (K -> A)) = (@eq (K -> A)).
Proof. exact (eq_refl (@eq (K -> A))). Qed.
Lemma lem4452783 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term68 A K k f) = (term69 A K k f).
Proof. exact (MK_COMB (@lem4452782 A K) (@lem4452781 A K k f)). Qed.
Lemma lem4452784 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term38 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term38 A K k f)). Qed.
Lemma lem4452785 {A K : Type'} (k : K -> Prop) (f : K -> A) : ((term66 A K k f) = (term38 A K k f)) = ((term38 A K k f) = (@RESTRICTION K A k f)).
Proof. exact (MK_COMB (@lem4452783 A K k f) (@lem4452784 A K k f)). Qed.
Lemma lem4452786 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term38 A K k f) = (@RESTRICTION K A k f).
Proof. exact (EQ_MP (@lem4452785 A K k f) (@lem4452777 A K k f)). Qed.
Lemma lem4452787 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4452788 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term70 A K k f i) = (@RESTRICTION K A k f i).
Proof. exact (MK_COMB (@lem4452786 A K k f) (@lem4452787 K i)). Qed.
Lemma lem4452789 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem4452790 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : (term71 A K P k f i) = (term72 A K P k f i).
Proof. exact (MK_COMB (@lem4452789 A K P i) (@lem4452788 A K k f i)). Qed.
Lemma lem4452791 {K : Type'} (i : K) (k : K -> Prop) : (term73 K i k) = (term73 K i k).
Proof. exact (eq_refl (term73 K i k)). Qed.
Lemma lem4452792 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : (term74 A K P k f i) = (term75 A K P k f i).
Proof. exact (MK_COMB (@lem4452791 K i k) (@lem4452790 A K P k f i)). Qed.
Lemma lem4452795 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) : (term76 A K P k f) = (term77 A K P k f).
Proof. exact (fun_ext (fun i : K => @lem4452792 A K P k f i)). Qed.
Lemma lem4452796 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4452797 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) : (term58 A K P k f) = (term78 A K P k f).
Proof. exact (MK_COMB (@lem4452796 K) (@lem4452795 A K P k f)). Qed.
Lemma lem4452802 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term56 A K k f s) = (term56 A K k f s).
Proof. exact (eq_refl (term56 A K k f s)). Qed.
Lemma lem4452803 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) (f : K -> A) : (term60 A K s P k f) = (term79 A K s P k f).
Proof. exact (MK_COMB (@lem4452802 A K k f s) (@lem4452797 A K P k f)). Qed.
Lemma lem4452806 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term62 A K s P k) = (term80 A K s P k).
Proof. exact (fun_ext (fun f : K -> A => @lem4452803 A K s P k f)). Qed.
Lemma lem4452807 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4452808 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term63 A K s P k) = (term81 A K s P k).
Proof. exact (MK_COMB (@lem4452807 A K) (@lem4452806 A K s P k)). Qed.
Lemma lem4452813 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term26 A K s k P) = (term81 A K s P k).
Proof. exact (TRANS (@lem4452755 A K s P k) (@lem4452808 A K s P k)). Qed.
Lemma lem4452814 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term25 A K s k P) = (term81 A K s P k).
Proof. exact (TRANS (@lem4452719 A K s k P) (@lem4452813 A K s P k)). Qed.
Lemma lem4452815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4452816 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : (term82 A K s k P) = (term83 A K s P k).
Proof. exact (MK_COMB (@lem4452815) (@lem4452814 A K s P k)). Qed.
Lemma lem4452829 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term84 A K k s P) = (term84 A K k s P).
Proof. exact (eq_refl (term84 A K k s P)). Qed.
Lemma lem4452830 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term25 A K s k P) = (term84 A K k s P)) = ((term81 A K s P k) = (term84 A K k s P)).
Proof. exact (MK_COMB (@lem4452816 A K s P k) (@lem4452829 A K k s P)). Qed.
Lemma lem4452833 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term81 A K s P k) = (term84 A K k s P)) = ((term25 A K s k P) = (term84 A K k s P)).
Proof. exact (SYM (@lem4452830 A K k s P)). Qed.
Lemma lem4452876 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term85 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4452877 (p : Prop) (q : Prop) (p' : Prop) : term86 p q p'.
Proof. exact (fun q' : Prop => @lem4452876 p q p' q'). Qed.
Lemma lem4452878 (p : Prop) (q : Prop) : term87 p q.
Proof. exact (fun p' : Prop => @lem4452877 p q p'). Qed.
Lemma lem4452879 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : term88 A K P k f i.
Proof. exact (@lem4452878 (@IN K i k) (term72 A K P k f i)). Qed.
Lemma lem4452880 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) (p' : Prop) : term89 A K P k f i p'.
Proof. exact (@lem4452879 A K P k f i p'). Qed.
Lemma lem4452881 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) (p' : Prop) : (term89 A K P k f i p') = (term90 A K P k f i p').
Proof. exact (eq_refl (term89 A K P k f i p')). Qed.
Lemma lem4452882 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) (p' : Prop) : term90 A K P k f i p'.
Proof. exact (EQ_MP (@lem4452881 A K P k f i p') (@lem4452880 A K P k f i p')). Qed.
Lemma lem4452883 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) (p' : Prop) (q' : Prop) : term91 A K P k f i p' q'.
Proof. exact (@lem4452882 A K P k f i p' q'). Qed.
Lemma lem4452884 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) (p' : Prop) (q' : Prop) : (term91 A K P k f i p' q') = (term92 A K P k f i p' q').
Proof. exact (eq_refl (term91 A K P k f i p' q')). Qed.
Lemma lem4452885 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) (p' : Prop) (q' : Prop) : term92 A K P k f i p' q'.
Proof. exact (EQ_MP (@lem4452884 A K P k f i p' q') (@lem4452883 A K P k f i p' q')). Qed.
Lemma lem4452886 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4452887 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) (k : K -> Prop) (q' : Prop) : term93 A K P f i k q'.
Proof. exact (@lem4452885 A K P k f i (@IN K i k) q'). Qed.
Lemma lem4452888 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) (k : K -> Prop) (q' : Prop) : term94 A K P f i k q'.
Proof. exact (@lem4452887 A K P f i k q' (@lem4452886 K i k)). Qed.
Lemma lem4452889 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4452890 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem4452893 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4452644 A B s f x) (@lem4452643 A B s f x)). Qed.
Lemma lem4452894 {A K : Type'} (s : K -> Prop) (f : K -> A) (x : K) : (@RESTRICTION K A s f x) = (term95 A K s f x).
Proof. exact (@lem4452893 K A s f x). Qed.
Lemma lem4452895 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (@RESTRICTION K A k f i) = (term95 A K k f i).
Proof. exact (@lem4452894 A K k f i). Qed.
Lemma lem4452897 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term96 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4452898 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term97 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4452897 _2963 g t e g' t' e'). Qed.
Lemma lem4452899 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term98 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4452898 _2963 g t e g' t'). Qed.
Lemma lem4452900 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term99 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4452899 _2963 g t e g'). Qed.
Lemma lem4452901 {A : Type'} (g : Prop) (t : A) (e : A) : term99 A g t e.
Proof. exact (@lem4452900 A g t e). Qed.
Lemma lem4452902 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : term100 A K k f i.
Proof. exact (@lem4452901 A (@IN K i k) (f i) (@ARB A)). Qed.
Lemma lem4452903 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : term101 A K k f i g'.
Proof. exact (@lem4452902 A K k f i g'). Qed.
Lemma lem4452904 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : (term101 A K k f i g') = (term102 A K k f i g').
Proof. exact (eq_refl (term101 A K k f i g')). Qed.
Lemma lem4452905 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : term102 A K k f i g'.
Proof. exact (EQ_MP (@lem4452904 A K k f i g') (@lem4452903 A K k f i g')). Qed.
Lemma lem4452906 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : term103 A K k f i g' t'.
Proof. exact (@lem4452905 A K k f i g' t'). Qed.
Lemma lem4452907 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : (term103 A K k f i g' t') = (term104 A K k f i g' t').
Proof. exact (eq_refl (term103 A K k f i g' t')). Qed.
Lemma lem4452908 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : term104 A K k f i g' t'.
Proof. exact (EQ_MP (@lem4452907 A K k f i g' t') (@lem4452906 A K k f i g' t')). Qed.
Lemma lem4452909 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : term105 A K k f i g' t' e'.
Proof. exact (@lem4452908 A K k f i g' t' e'). Qed.
Lemma lem4452910 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : (term105 A K k f i g' t' e') = (term106 A K k f i g' t' e').
Proof. exact (eq_refl (term105 A K k f i g' t' e')). Qed.
Lemma lem4452911 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : term106 A K k f i g' t' e'.
Proof. exact (EQ_MP (@lem4452910 A K k f i g' t' e') (@lem4452909 A K k f i g' t' e')). Qed.
Lemma lem4452913 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem4452890 K i k) (@lem4452889 K i k h1)). Qed.
Lemma lem4452914 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (t' : A) (e' : A) : term107 A K k f i t' e'.
Proof. exact (@lem4452911 A K k f i True t' e'). Qed.
Lemma lem4452915 {A K : Type'} (f : K -> A) (t' : A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term108 A K k f i t' e'.
Proof. exact (@lem4452914 A K k f i t' e' (@lem4452913 K i k h1)). Qed.
Lemma lem4452921 {A K : Type'} (f : K -> A) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4452922 {A K : Type'} (f : K -> A) (i : K) : term109 A K f i.
Proof. exact (fun h0 : True => @lem4452921 A K f i). Qed.
Lemma lem4452923 {A K : Type'} (f : K -> A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term110 A K k f i e'.
Proof. exact (@lem4452915 A K f (f i) e' i k h1). Qed.
Lemma lem4452924 {A K : Type'} (f : K -> A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term111 A K k f i e'.
Proof. exact (@lem4452923 A K f e' i k h1 (@lem4452922 A K f i)). Qed.
Lemma lem4452928 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4452929 {A : Type'} : term112 A.
Proof. exact (fun h0 : ~ True => @lem4452928 A). Qed.
Lemma lem4452930 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term113 A K k f i.
Proof. exact (@lem4452924 A K f (@ARB A) i k h1). Qed.
Lemma lem4452931 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term95 A K k f i) = (term114 A K f i).
Proof. exact (@lem4452930 A K f i k h1 (@lem4452929 A)). Qed.
Lemma lem4452933 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4452934 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4452933 A t2 t1). Qed.
Lemma lem4452935 {A K : Type'} (f : K -> A) (i : K) : (term114 A K f i) = (f i).
Proof. exact (@lem4452934 A (@ARB A) (f i)). Qed.
Lemma lem4452936 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term95 A K k f i) = (f i).
Proof. exact (TRANS (@lem4452931 A K f i k h1) (@lem4452935 A K f i)). Qed.
Lemma lem4452937 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@RESTRICTION K A k f i) = (f i).
Proof. exact (TRANS (@lem4452895 A K k f i) (@lem4452936 A K f i k h1)). Qed.
Lemma lem4452938 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem4452939 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term72 A K P k f i) = (term115 A K P f i).
Proof. exact (MK_COMB (@lem4452938 A K P i) (@lem4452937 A K f i k h1)). Qed.
Lemma lem4452940 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : term116 A K k P f i.
Proof. exact (fun h0 : @IN K i k => @lem4452939 A K P f i k h0). Qed.
Lemma lem4452941 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : term117 A K k P f i.
Proof. exact (@lem4452888 A K P f i k (term115 A K P f i)). Qed.
Lemma lem4452942 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term75 A K P k f i) = (term118 A K k P f i).
Proof. exact (@lem4452941 A K k P f i (@lem4452940 A K k P f i)). Qed.
Lemma lem4452966 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term77 A K P k f) = (term119 A K k P f).
Proof. exact (fun_ext (fun i : K => @lem4452942 A K k P f i)). Qed.
Lemma lem4452990 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4452991 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term78 A K P k f) = (term20 A K k P f).
Proof. exact (MK_COMB (@lem4452990 K) (@lem4452966 A K k P f)). Qed.
Lemma lem4453019 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term56 A K k f s) = (term56 A K k f s).
Proof. exact (eq_refl (term56 A K k f s)). Qed.
Lemma lem4453020 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term79 A K s P k f) = (term120 A K s k P f).
Proof. exact (MK_COMB (@lem4453019 A K k f s) (@lem4452991 A K k P f)). Qed.
Lemma lem4453077 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term80 A K s P k) = (term121 A K s k P).
Proof. exact (fun_ext (fun f : K -> A => @lem4453020 A K s k P f)). Qed.
Lemma lem4453134 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4453135 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term81 A K s P k) = (term122 A K s k P).
Proof. exact (MK_COMB (@lem4453134 A K) (@lem4453077 A K s k P)). Qed.
Lemma lem4453196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4453197 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term83 A K s P k) = (term123 A K s k P).
Proof. exact (MK_COMB (@lem4453196) (@lem4453135 A K s k P)). Qed.
Lemma lem4453297 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term84 A K k s P) = (term84 A K k s P).
Proof. exact (eq_refl (term84 A K k s P)). Qed.
Lemma lem4453298 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term81 A K s P k) = (term84 A K k s P)) = ((term122 A K s k P) = (term84 A K k s P)).
Proof. exact (MK_COMB (@lem4453197 A K s k P) (@lem4453297 A K k s P)). Qed.
Lemma lem4453400 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term122 A K s k P) = (term84 A K k s P)) = ((term81 A K s P k) = (term84 A K k s P)).
Proof. exact (SYM (@lem4453298 A K k s P)). Qed.
Lemma lem4453402 (p : Prop) : p = (term124 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4453403 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term122 A K s k P) = (term84 A K k s P)) = (term125 A K k s P).
Proof. exact (@lem4453402 ((term122 A K s k P) = (term84 A K k s P))). Qed.
Lemma lem4453404 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term125 A K k s P) = ((term122 A K s k P) = (term84 A K k s P)).
Proof. exact (SYM (@lem4453403 A K k s P)). Qed.
Lemma lem4453405 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : term126 A K k s P.
Proof. exact (h1). Qed.
Lemma lem4453408 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term125 A K k s P) : term125 A K k s P.
Proof. exact (h1). Qed.
Lemma lem4453409 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term127 A K k s P.
Proof. exact (fun h0 : term125 A K k s P => @lem4453408 A K k s P h0). Qed.
Lemma lem4453410 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term127 A K k s P) : term127 A K k s P.
Proof. exact (h1). Qed.
Lemma lem4453411 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term125 A K k s P) : term125 A K k s P.
Proof. exact (h1). Qed.
Lemma lem4453412 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term125 A K k s P) (h2 : term127 A K k s P) : term125 A K k s P.
Proof. exact (@lem4453410 A K k s P h2 (@lem4453411 A K k s P h1)). Qed.
Lemma lem4453413 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term125 A K k s P) : term128 A K k s P.
Proof. exact (fun h0 : term127 A K k s P => @lem4453412 A K k s P h1 h0). Qed.
Lemma lem4453414 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term127 A K k s P) : term127 A K k s P.
Proof. exact (h1). Qed.
Lemma lem4453415 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term125 A K k s P) (h2 : term127 A K k s P) : term125 A K k s P.
Proof. exact (@lem4453413 A K k s P h1 (@lem4453414 A K k s P h2)). Qed.
Lemma lem4453416 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term127 A K k s P) : term127 A K k s P.
Proof. exact (fun h0 : term125 A K k s P => @lem4453415 A K k s P h0 h1). Qed.
Lemma lem4453417 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term129 A K k s P.
Proof. exact (fun h0 : term127 A K k s P => @lem4453416 A K k s P h0). Qed.
Lemma lem4453420 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term127 A K k s P.
Proof. exact (@lem4453417 A K k s P (@lem4453409 A K k s P)). Qed.
Lemma lem4453421 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term127 A K k s P.
Proof. exact (@lem4453420 A K k s P). Qed.
Lemma lem4453435 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4453436 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term125 A K k s P) = (term130 A K k s P).
Proof. exact (@lem4453435 (term126 A K k s P)). Qed.
Lemma lem4453438 (t : Prop) : (term131 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4453439 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term130 A K k s P) = ((term122 A K s k P) = (term84 A K k s P)).
Proof. exact (@lem4453438 ((term122 A K s k P) = (term84 A K k s P))). Qed.
Lemma lem4453440 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term125 A K k s P) = ((term122 A K s k P) = (term84 A K k s P)).
Proof. exact (TRANS (@lem4453436 A K k s P) (@lem4453439 A K k s P)). Qed.
Lemma lem4453559 {A K : Type'} (s : type1470 A K) (P : type1470 A K) : (term132 A K s P) = (term133 A K s P).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4453440 A K k s P)). Qed.
Lemma lem4453560 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4453561 {A K : Type'} (s : type1470 A K) (P : type1470 A K) : (term134 A K s P) = (term135 A K s P).
Proof. exact (MK_COMB (@lem4453560 K) (@lem4453559 A K s P)). Qed.
Lemma lem4453566 {A K : Type'} (P : type1470 A K) : (term136 A K P) = (term137 A K P).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4453561 A K s P)). Qed.
Lemma lem4453567 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4453568 {A K : Type'} (P : type1470 A K) : (term138 A K P) = (term139 A K P).
Proof. exact (MK_COMB (@lem4453567 A K) (@lem4453566 A K P)). Qed.
Lemma lem4453573 {A K : Type'} : (term140 A K) = (term141 A K).
Proof. exact (fun_ext (fun P : type1470 A K => @lem4453568 A K P)). Qed.
Lemma lem4453574 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4453583 {A K : Type'} : (term142 A K) = (term143 A K).
Proof. exact (MK_COMB (@lem4453574 A K) (@lem4453573 A K)). Qed.
Lemma lem4453588 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term144 A K s P i x) = (term144 A K s P i x).
Proof. exact (eq_refl (term144 A K s P i x)). Qed.
Lemma lem4453589 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term145 A K s P i) = (term145 A K s P i).
Proof. exact (fun_ext (fun x : A => @lem4453588 A K s P i x)). Qed.
Lemma lem4453590 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4453591 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term146 A K s P i) = (term146 A K s P i).
Proof. exact (MK_COMB (@lem4453590 A) (@lem4453589 A K s P i)). Qed.
Lemma lem4453594 {K : Type'} (i : K) (k : K -> Prop) : (term73 K i k) = (term73 K i k).
Proof. exact (eq_refl (term73 K i k)). Qed.
Lemma lem4453595 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term147 A K k s P i) = (term147 A K k s P i).
Proof. exact (MK_COMB (@lem4453594 K i k) (@lem4453591 A K s P i)). Qed.
Lemma lem4453596 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term148 A K k s P) = (term148 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4453595 A K k s P i)). Qed.
Lemma lem4453597 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4453598 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term84 A K k s P) = (term84 A K k s P).
Proof. exact (MK_COMB (@lem4453597 K) (@lem4453596 A K k s P)). Qed.
Lemma lem4453603 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term118 A K k P f i) = (term118 A K k P f i).
Proof. exact (eq_refl (term118 A K k P f i)). Qed.
Lemma lem4453604 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term119 A K k P f) = (term119 A K k P f).
Proof. exact (fun_ext (fun i : K => @lem4453603 A K k P f i)). Qed.
Lemma lem4453605 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4453606 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term20 A K k P f) = (term20 A K k P f).
Proof. exact (MK_COMB (@lem4453605 K) (@lem4453604 A K k P f)). Qed.
Lemma lem4453611 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term149 A K k f s i) = (term149 A K k f s i).
Proof. exact (eq_refl (term149 A K k f s i)). Qed.
Lemma lem4453612 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term150 A K k f s) = (term150 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4453611 A K k f s i)). Qed.
Lemma lem4453613 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4453614 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term35 A K k f s) = (term35 A K k f s).
Proof. exact (MK_COMB (@lem4453613 K) (@lem4453612 A K k f s)). Qed.
Lemma lem4453615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4453616 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term56 A K k f s) = (term56 A K k f s).
Proof. exact (MK_COMB (@lem4453615) (@lem4453614 A K k f s)). Qed.
Lemma lem4453617 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term120 A K s k P f) = (term120 A K s k P f).
Proof. exact (MK_COMB (@lem4453616 A K k f s) (@lem4453606 A K k P f)). Qed.
Lemma lem4453618 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term121 A K s k P) = (term121 A K s k P).
Proof. exact (fun_ext (fun f : K -> A => @lem4453617 A K s k P f)). Qed.
Lemma lem4453619 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4453620 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term122 A K s k P) = (term122 A K s k P).
Proof. exact (MK_COMB (@lem4453619 A K) (@lem4453618 A K s k P)). Qed.
Lemma lem4453621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4453622 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term123 A K s k P) = (term123 A K s k P).
Proof. exact (MK_COMB (@lem4453621) (@lem4453620 A K s k P)). Qed.
Lemma lem4453623 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term122 A K s k P) = (term84 A K k s P)) = ((term122 A K s k P) = (term84 A K k s P)).
Proof. exact (MK_COMB (@lem4453622 A K s k P) (@lem4453598 A K k s P)). Qed.
Lemma lem4453624 {A K : Type'} (s : type1470 A K) (P : type1470 A K) : (term133 A K s P) = (term133 A K s P).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4453623 A K k s P)). Qed.
Lemma lem4453625 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4453626 {A K : Type'} (s : type1470 A K) (P : type1470 A K) : (term135 A K s P) = (term135 A K s P).
Proof. exact (MK_COMB (@lem4453625 K) (@lem4453624 A K s P)). Qed.
Lemma lem4453627 {A K : Type'} (P : type1470 A K) : (term137 A K P) = (term137 A K P).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4453626 A K s P)). Qed.
Lemma lem4453628 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4453629 {A K : Type'} (P : type1470 A K) : (term139 A K P) = (term139 A K P).
Proof. exact (MK_COMB (@lem4453628 A K) (@lem4453627 A K P)). Qed.
Lemma lem4453630 {A K : Type'} : (term141 A K) = (term141 A K).
Proof. exact (fun_ext (fun P : type1470 A K => @lem4453629 A K P)). Qed.
Lemma lem4453631 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4453632 {A K : Type'} : (term143 A K) = (term143 A K).
Proof. exact (MK_COMB (@lem4453631 A K) (@lem4453630 A K)). Qed.
Lemma lem4453693 {A K : Type'} : (term142 A K) = (term143 A K).
Proof. exact (TRANS (@lem4453583 A K) (@lem4453632 A K)). Qed.
Lemma lem4453694 {A K : Type'} : (term143 A K) = (term142 A K).
Proof. exact (SYM (@lem4453693 A K)). Qed.
Lemma lem4453696 (p : Prop) : p = (term124 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4453697 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term122 A K s k P) = (term84 A K k s P)) = (term125 A K k s P).
Proof. exact (@lem4453696 ((term122 A K s k P) = (term84 A K k s P))). Qed.
Lemma lem4453698 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term125 A K k s P) = ((term122 A K s k P) = (term84 A K k s P)).
Proof. exact (SYM (@lem4453697 A K k s P)). Qed.
Lemma lem4453699 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : term126 A K k s P.
Proof. exact (h1). Qed.
Lemma lem4453708 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term151 A K k f s i) = (term152 A K k f s i).
Proof. exact (@lem17362 (@IN K i k) (term153 A K f s i)). Qed.
Lemma lem4453713 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term149 A K k f s i) = (term154 A K k f s i).
Proof. exact (@lem17265 (@IN K i k) (term153 A K f s i)). Qed.
Lemma lem4453714 {K : Type'} (P : K -> Prop) : (term155 K P) = (term156 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4453715 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term157 A K k f s) = (term158 A K k f s).
Proof. exact (@lem4453714 K (term150 A K k f s)). Qed.
Lemma lem4453716 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term159 A K k f s i) = (term149 A K k f s i).
Proof. exact (eq_refl (term159 A K k f s i)). Qed.
Lemma lem4453717 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4453718 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term160 A K k f s i) = (term151 A K k f s i).
Proof. exact (MK_COMB (@lem4453717) (@lem4453716 A K k f s i)). Qed.
Lemma lem4453719 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term160 A K k f s i) = (term152 A K k f s i).
Proof. exact (TRANS (@lem4453718 A K k f s i) (@lem4453708 A K k f s i)). Qed.
Lemma lem4453720 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term161 A K k f s) = (term162 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4453719 A K k f s i)). Qed.
Lemma lem4453721 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4453722 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term158 A K k f s) = (term163 A K k f s).
Proof. exact (MK_COMB (@lem4453721 K) (@lem4453720 A K k f s)). Qed.
Lemma lem4453723 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term157 A K k f s) = (term163 A K k f s).
Proof. exact (TRANS (@lem4453715 A K k f s) (@lem4453722 A K k f s)). Qed.
Lemma lem4453724 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term150 A K k f s) = (term164 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4453713 A K k f s i)). Qed.
Lemma lem4453725 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4453726 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term35 A K k f s) = (term165 A K k f s).
Proof. exact (MK_COMB (@lem4453725 K) (@lem4453724 A K k f s)). Qed.
Lemma lem4453735 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term166 A K k P f i) = (term167 A K k P f i).
Proof. exact (@lem17362 (@IN K i k) (term115 A K P f i)). Qed.
Lemma lem4453740 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term118 A K k P f i) = (term168 A K k P f i).
Proof. exact (@lem17265 (@IN K i k) (term115 A K P f i)). Qed.
Lemma lem4453741 {K : Type'} (P : K -> Prop) : (term155 K P) = (term156 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4453742 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term169 A K k P f) = (term170 A K k P f).
Proof. exact (@lem4453741 K (term119 A K k P f)). Qed.
Lemma lem4453743 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term171 A K k P f i) = (term118 A K k P f i).
Proof. exact (eq_refl (term171 A K k P f i)). Qed.
Lemma lem4453744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4453745 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term172 A K k P f i) = (term166 A K k P f i).
Proof. exact (MK_COMB (@lem4453744) (@lem4453743 A K k P f i)). Qed.
Lemma lem4453746 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term172 A K k P f i) = (term167 A K k P f i).
Proof. exact (TRANS (@lem4453745 A K k P f i) (@lem4453735 A K k P f i)). Qed.
Lemma lem4453747 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term173 A K k P f) = (term174 A K k P f).
Proof. exact (fun_ext (fun i : K => @lem4453746 A K k P f i)). Qed.
Lemma lem4453748 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4453749 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term170 A K k P f) = (term175 A K k P f).
Proof. exact (MK_COMB (@lem4453748 K) (@lem4453747 A K k P f)). Qed.
Lemma lem4453750 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term169 A K k P f) = (term175 A K k P f).
Proof. exact (TRANS (@lem4453742 A K k P f) (@lem4453749 A K k P f)). Qed.
Lemma lem4453751 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term119 A K k P f) = (term176 A K k P f).
Proof. exact (fun_ext (fun i : K => @lem4453740 A K k P f i)). Qed.
Lemma lem4453752 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4453753 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term20 A K k P f) = (term177 A K k P f).
Proof. exact (MK_COMB (@lem4453752 K) (@lem4453751 A K k P f)). Qed.
Lemma lem4453754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4453755 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term178 A K k f s) = (term179 A K k f s).
Proof. exact (MK_COMB (@lem4453754) (@lem4453723 A K k f s)). Qed.
Lemma lem4453756 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term180 A K s k P f) = (term181 A K s k P f).
Proof. exact (MK_COMB (@lem4453755 A K k f s) (@lem4453750 A K k P f)). Qed.
Lemma lem4453757 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term182 A K s k P f) = (term180 A K s k P f).
Proof. exact (@lem17045 (term35 A K k f s) (term20 A K k P f)). Qed.
Lemma lem4453758 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term182 A K s k P f) = (term181 A K s k P f).
Proof. exact (TRANS (@lem4453757 A K s k P f) (@lem4453756 A K s k P f)). Qed.
Lemma lem4453759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4453760 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term56 A K k f s) = (term183 A K k f s).
Proof. exact (MK_COMB (@lem4453759) (@lem4453726 A K k f s)). Qed.
Lemma lem4453761 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term120 A K s k P f) = (term184 A K s k P f).
Proof. exact (MK_COMB (@lem4453760 A K k f s) (@lem4453753 A K k P f)). Qed.
Lemma lem4453762 {A K : Type'} (P : type805 A K) : (term185 A K P) = (term186 A K P).
Proof. exact (@lem18394 (K -> A) P). Qed.
Lemma lem4453763 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term187 A K s k P) = (term188 A K s k P).
Proof. exact (@lem4453762 A K (term121 A K s k P)). Qed.
Lemma lem4453764 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term189 A K s k P f) = (term120 A K s k P f).
Proof. exact (eq_refl (term189 A K s k P f)). Qed.
Lemma lem4453765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4453766 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term190 A K s k P f) = (term182 A K s k P f).
Proof. exact (MK_COMB (@lem4453765) (@lem4453764 A K s k P f)). Qed.
Lemma lem4453767 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term190 A K s k P f) = (term181 A K s k P f).
Proof. exact (TRANS (@lem4453766 A K s k P f) (@lem4453758 A K s k P f)). Qed.
Lemma lem4453768 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term191 A K s k P) = (term192 A K s k P).
Proof. exact (fun_ext (fun f : K -> A => @lem4453767 A K s k P f)). Qed.
Lemma lem4453769 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4453770 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term188 A K s k P) = (term193 A K s k P).
Proof. exact (MK_COMB (@lem4453769 A K) (@lem4453768 A K s k P)). Qed.
Lemma lem4453771 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term187 A K s k P) = (term193 A K s k P).
Proof. exact (TRANS (@lem4453763 A K s k P) (@lem4453770 A K s k P)). Qed.
Lemma lem4453772 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term121 A K s k P) = (term194 A K s k P).
Proof. exact (fun_ext (fun f : K -> A => @lem4453761 A K s k P f)). Qed.
Lemma lem4453773 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4453774 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term122 A K s k P) = (term195 A K s k P).
Proof. exact (MK_COMB (@lem4453773 A K) (@lem4453772 A K s k P)). Qed.
Lemma lem4453785 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term196 A K s P i x) = (term197 A K s P i x).
Proof. exact (@lem17045 (term198 A K x s i) (P i x)). Qed.
Lemma lem4453788 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term144 A K s P i x) = (term144 A K s P i x).
Proof. exact (eq_refl (term144 A K s P i x)). Qed.
Lemma lem4453789 {A : Type'} (P : A -> Prop) : (term199 A P) = (term200 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4453790 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term201 A K s P i) = (term202 A K s P i).
Proof. exact (@lem4453789 A (term145 A K s P i)). Qed.
Lemma lem4453791 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term203 A K s P i x) = (term144 A K s P i x).
Proof. exact (eq_refl (term203 A K s P i x)). Qed.
Lemma lem4453792 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4453793 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term204 A K s P i x) = (term196 A K s P i x).
Proof. exact (MK_COMB (@lem4453792) (@lem4453791 A K s P i x)). Qed.
Lemma lem4453794 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term204 A K s P i x) = (term197 A K s P i x).
Proof. exact (TRANS (@lem4453793 A K s P i x) (@lem4453785 A K s P i x)). Qed.
Lemma lem4453795 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term205 A K s P i) = (term206 A K s P i).
Proof. exact (fun_ext (fun x : A => @lem4453794 A K s P i x)). Qed.
Lemma lem4453796 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4453797 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term202 A K s P i) = (term207 A K s P i).
Proof. exact (MK_COMB (@lem4453796 A) (@lem4453795 A K s P i)). Qed.
Lemma lem4453798 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term201 A K s P i) = (term207 A K s P i).
Proof. exact (TRANS (@lem4453790 A K s P i) (@lem4453797 A K s P i)). Qed.
Lemma lem4453799 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term145 A K s P i) = (term145 A K s P i).
Proof. exact (fun_ext (fun x : A => @lem4453788 A K s P i x)). Qed.
Lemma lem4453800 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4453801 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term146 A K s P i) = (term146 A K s P i).
Proof. exact (MK_COMB (@lem4453800 A) (@lem4453799 A K s P i)). Qed.
Lemma lem4453803 {K : Type'} (i : K) (k : K -> Prop) : (term208 K i k) = (term208 K i k).
Proof. exact (eq_refl (term208 K i k)). Qed.
Lemma lem4453804 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term209 A K k s P i) = (term210 A K k s P i).
Proof. exact (MK_COMB (@lem4453803 K i k) (@lem4453798 A K s P i)). Qed.
Lemma lem4453805 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term211 A K k s P i) = (term209 A K k s P i).
Proof. exact (@lem17362 (@IN K i k) (term146 A K s P i)). Qed.
Lemma lem4453806 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term211 A K k s P i) = (term210 A K k s P i).
Proof. exact (TRANS (@lem4453805 A K k s P i) (@lem4453804 A K k s P i)). Qed.
Lemma lem4453808 {K : Type'} (i : K) (k : K -> Prop) : (term212 K i k) = (term212 K i k).
Proof. exact (eq_refl (term212 K i k)). Qed.
Lemma lem4453809 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term213 A K k s P i) = (term213 A K k s P i).
Proof. exact (MK_COMB (@lem4453808 K i k) (@lem4453801 A K s P i)). Qed.
Lemma lem4453810 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term147 A K k s P i) = (term213 A K k s P i).
Proof. exact (@lem17265 (@IN K i k) (term146 A K s P i)). Qed.
Lemma lem4453811 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term147 A K k s P i) = (term213 A K k s P i).
Proof. exact (TRANS (@lem4453810 A K k s P i) (@lem4453809 A K k s P i)). Qed.
Lemma lem4453812 {K : Type'} (P : K -> Prop) : (term155 K P) = (term156 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4453813 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term214 A K k s P) = (term215 A K k s P).
Proof. exact (@lem4453812 K (term148 A K k s P)). Qed.
Lemma lem4453814 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term216 A K k s P i) = (term147 A K k s P i).
Proof. exact (eq_refl (term216 A K k s P i)). Qed.
Lemma lem4453815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4453816 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term217 A K k s P i) = (term211 A K k s P i).
Proof. exact (MK_COMB (@lem4453815) (@lem4453814 A K k s P i)). Qed.
Lemma lem4453817 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term217 A K k s P i) = (term210 A K k s P i).
Proof. exact (TRANS (@lem4453816 A K k s P i) (@lem4453806 A K k s P i)). Qed.
Lemma lem4453818 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term218 A K k s P) = (term219 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4453817 A K k s P i)). Qed.
Lemma lem4453819 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4453820 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term215 A K k s P) = (term220 A K k s P).
Proof. exact (MK_COMB (@lem4453819 K) (@lem4453818 A K k s P)). Qed.
Lemma lem4453821 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term214 A K k s P) = (term220 A K k s P).
Proof. exact (TRANS (@lem4453813 A K k s P) (@lem4453820 A K k s P)). Qed.
Lemma lem4453822 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term148 A K k s P) = (term221 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4453811 A K k s P i)). Qed.
Lemma lem4453823 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4453824 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term84 A K k s P) = (term222 A K k s P).
Proof. exact (MK_COMB (@lem4453823 K) (@lem4453822 A K k s P)). Qed.
Lemma lem4453825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4453826 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term223 A K s k P) = (term224 A K s k P).
Proof. exact (MK_COMB (@lem4453825) (@lem4453771 A K s k P)). Qed.
Lemma lem4453827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term225 A K k s P) = (term226 A K k s P).
Proof. exact (MK_COMB (@lem4453826 A K s k P) (@lem4453824 A K k s P)). Qed.
Lemma lem4453828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4453829 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term227 A K s k P) = (term228 A K s k P).
Proof. exact (MK_COMB (@lem4453828) (@lem4453774 A K s k P)). Qed.
Lemma lem4453830 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term229 A K k s P) = (term230 A K k s P).
Proof. exact (MK_COMB (@lem4453829 A K s k P) (@lem4453821 A K k s P)). Qed.
Lemma lem4453831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4453832 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term231 A K k s P) = (term232 A K k s P).
Proof. exact (MK_COMB (@lem4453831) (@lem4453830 A K k s P)). Qed.
Lemma lem4453833 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term233 A K k s P) = (term234 A K k s P).
Proof. exact (MK_COMB (@lem4453832 A K k s P) (@lem4453827 A K k s P)). Qed.
Lemma lem4453834 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term126 A K k s P) = (term233 A K k s P).
Proof. exact (@lem17646 (term122 A K s k P) (term84 A K k s P)). Qed.
Lemma lem4453835 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term126 A K k s P) = (term234 A K k s P).
Proof. exact (TRANS (@lem4453834 A K k s P) (@lem4453833 A K k s P)). Qed.
Lemma lem4454318 {A : Type'} (P : A -> Prop) (Q : Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4454319 {A K : Type'} (P : type805 A K) (Q : Prop) : (term237 A K P Q) = (term238 A K P Q).
Proof. exact (@lem4454318 (K -> A) P Q). Qed.
Lemma lem4454320 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term239 A K k s P) = (term240 A K k s P).
Proof. exact (@lem4454319 A K (term194 A K s k P) (term220 A K k s P)). Qed.
Lemma lem4454321 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term241 A K s k P f) = (term184 A K s k P f).
Proof. exact (eq_refl (term241 A K s k P f)). Qed.
Lemma lem4454322 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term242 A K s k P) = (term194 A K s k P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454321 A K s k P f)). Qed.
Lemma lem4454323 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454324 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term243 A K s k P) = (term195 A K s k P).
Proof. exact (MK_COMB (@lem4454323 A K) (@lem4454322 A K s k P)). Qed.
Lemma lem4454325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454326 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term244 A K s k P) = (term228 A K s k P).
Proof. exact (MK_COMB (@lem4454325) (@lem4454324 A K s k P)). Qed.
Lemma lem4454327 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term220 A K k s P) = (term220 A K k s P).
Proof. exact (eq_refl (term220 A K k s P)). Qed.
Lemma lem4454328 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term239 A K k s P) = (term230 A K k s P).
Proof. exact (MK_COMB (@lem4454326 A K s k P) (@lem4454327 A K k s P)). Qed.
Lemma lem4454329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454330 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term245 A K k s P) = (term246 A K k s P).
Proof. exact (MK_COMB (@lem4454329) (@lem4454328 A K k s P)). Qed.
Lemma lem4454331 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term241 A K s k P f) = (term184 A K s k P f).
Proof. exact (eq_refl (term241 A K s k P f)). Qed.
Lemma lem4454332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454333 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term247 A K s k P f) = (term248 A K s k P f).
Proof. exact (MK_COMB (@lem4454332) (@lem4454331 A K s k P f)). Qed.
Lemma lem4454334 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term220 A K k s P) = (term220 A K k s P).
Proof. exact (eq_refl (term220 A K k s P)). Qed.
Lemma lem4454335 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term249 A K f k s P) = (term250 A K f k s P).
Proof. exact (MK_COMB (@lem4454333 A K s k P f) (@lem4454334 A K k s P)). Qed.
Lemma lem4454336 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term251 A K k s P) = (term252 A K k s P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454335 A K f k s P)). Qed.
Lemma lem4454337 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454338 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term240 A K k s P) = (term253 A K k s P).
Proof. exact (MK_COMB (@lem4454337 A K) (@lem4454336 A K k s P)). Qed.
Lemma lem4454339 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term239 A K k s P) = (term240 A K k s P)) = ((term230 A K k s P) = (term253 A K k s P)).
Proof. exact (MK_COMB (@lem4454330 A K k s P) (@lem4454338 A K k s P)). Qed.
Lemma lem4454340 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term230 A K k s P) = (term253 A K k s P).
Proof. exact (EQ_MP (@lem4454339 A K k s P) (@lem4454320 A K k s P)). Qed.
Lemma lem4454342 {A : Type'} (P : Prop) (Q : A -> Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4454343 {K : Type'} (P : Prop) (Q : K -> Prop) : (term254 K P Q) = (term255 K P Q).
Proof. exact (@lem4454342 K P Q). Qed.
Lemma lem4454344 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term256 A K f k s P) = (term257 A K f k s P).
Proof. exact (@lem4454343 K (term184 A K s k P f) (term219 A K k s P)). Qed.
Lemma lem4454345 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term258 A K k s P i) = (term210 A K k s P i).
Proof. exact (eq_refl (term258 A K k s P i)). Qed.
Lemma lem4454346 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term259 A K k s P) = (term219 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4454345 A K k s P i)). Qed.
Lemma lem4454347 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454348 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term260 A K k s P) = (term220 A K k s P).
Proof. exact (MK_COMB (@lem4454347 K) (@lem4454346 A K k s P)). Qed.
Lemma lem4454349 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term248 A K s k P f) = (term248 A K s k P f).
Proof. exact (eq_refl (term248 A K s k P f)). Qed.
Lemma lem4454350 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term256 A K f k s P) = (term250 A K f k s P).
Proof. exact (MK_COMB (@lem4454349 A K s k P f) (@lem4454348 A K k s P)). Qed.
Lemma lem4454351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454352 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term261 A K f k s P) = (term262 A K f k s P).
Proof. exact (MK_COMB (@lem4454351) (@lem4454350 A K f k s P)). Qed.
Lemma lem4454353 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term258 A K k s P i) = (term210 A K k s P i).
Proof. exact (eq_refl (term258 A K k s P i)). Qed.
Lemma lem4454354 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term248 A K s k P f) = (term248 A K s k P f).
Proof. exact (eq_refl (term248 A K s k P f)). Qed.
Lemma lem4454355 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term263 A K f k s P i) = (term264 A K f k s P i).
Proof. exact (MK_COMB (@lem4454354 A K s k P f) (@lem4454353 A K k s P i)). Qed.
Lemma lem4454356 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term265 A K f k s P) = (term266 A K f k s P).
Proof. exact (fun_ext (fun i : K => @lem4454355 A K f k s P i)). Qed.
Lemma lem4454357 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454358 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term257 A K f k s P) = (term267 A K f k s P).
Proof. exact (MK_COMB (@lem4454357 K) (@lem4454356 A K f k s P)). Qed.
Lemma lem4454359 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term256 A K f k s P) = (term257 A K f k s P)) = ((term250 A K f k s P) = (term267 A K f k s P)).
Proof. exact (MK_COMB (@lem4454352 A K f k s P) (@lem4454358 A K f k s P)). Qed.
Lemma lem4454360 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term250 A K f k s P) = (term267 A K f k s P).
Proof. exact (EQ_MP (@lem4454359 A K f k s P) (@lem4454344 A K f k s P)). Qed.
Lemma lem4454361 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term252 A K k s P) = (term268 A K k s P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454360 A K f k s P)). Qed.
Lemma lem4454362 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454363 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term253 A K k s P) = (term269 A K k s P).
Proof. exact (MK_COMB (@lem4454362 A K) (@lem4454361 A K k s P)). Qed.
Lemma lem4454364 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term230 A K k s P) = (term269 A K k s P).
Proof. exact (TRANS (@lem4454340 A K k s P) (@lem4454363 A K k s P)). Qed.
Lemma lem4454365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454366 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term232 A K k s P) = (term270 A K k s P).
Proof. exact (MK_COMB (@lem4454365) (@lem4454364 A K k s P)). Qed.
Lemma lem4454368 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4454369 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term271 K P Q) = (term272 K P Q).
Proof. exact (@lem4454368 K P Q). Qed.
Lemma lem4454370 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term273 A K s k P f) = (term274 A K s k P f).
Proof. exact (@lem4454369 K (term162 A K k f s) (term174 A K k P f)). Qed.
Lemma lem4454371 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term275 A K k f s i) = (term152 A K k f s i).
Proof. exact (eq_refl (term275 A K k f s i)). Qed.
Lemma lem4454372 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term276 A K k f s) = (term162 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4454371 A K k f s i)). Qed.
Lemma lem4454373 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454374 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term277 A K k f s) = (term163 A K k f s).
Proof. exact (MK_COMB (@lem4454373 K) (@lem4454372 A K k f s)). Qed.
Lemma lem4454375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454376 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term278 A K k f s) = (term179 A K k f s).
Proof. exact (MK_COMB (@lem4454375) (@lem4454374 A K k f s)). Qed.
Lemma lem4454377 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term279 A K k P f i) = (term167 A K k P f i).
Proof. exact (eq_refl (term279 A K k P f i)). Qed.
Lemma lem4454378 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term280 A K k P f) = (term174 A K k P f).
Proof. exact (fun_ext (fun i : K => @lem4454377 A K k P f i)). Qed.
Lemma lem4454379 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454380 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term281 A K k P f) = (term175 A K k P f).
Proof. exact (MK_COMB (@lem4454379 K) (@lem4454378 A K k P f)). Qed.
Lemma lem4454381 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term273 A K s k P f) = (term181 A K s k P f).
Proof. exact (MK_COMB (@lem4454376 A K k f s) (@lem4454380 A K k P f)). Qed.
Lemma lem4454382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454383 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term282 A K s k P f) = (term283 A K s k P f).
Proof. exact (MK_COMB (@lem4454382) (@lem4454381 A K s k P f)). Qed.
Lemma lem4454384 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term275 A K k f s i) = (term152 A K k f s i).
Proof. exact (eq_refl (term275 A K k f s i)). Qed.
Lemma lem4454385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454386 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term284 A K k f s i) = (term285 A K k f s i).
Proof. exact (MK_COMB (@lem4454385) (@lem4454384 A K k f s i)). Qed.
Lemma lem4454387 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term279 A K k P f i) = (term167 A K k P f i).
Proof. exact (eq_refl (term279 A K k P f i)). Qed.
Lemma lem4454388 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term286 A K s k P f i) = (term287 A K s k P f i).
Proof. exact (MK_COMB (@lem4454386 A K k f s i) (@lem4454387 A K k P f i)). Qed.
Lemma lem4454389 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term288 A K s k P f) = (term289 A K s k P f).
Proof. exact (fun_ext (fun i : K => @lem4454388 A K s k P f i)). Qed.
Lemma lem4454390 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454391 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term274 A K s k P f) = (term290 A K s k P f).
Proof. exact (MK_COMB (@lem4454390 K) (@lem4454389 A K s k P f)). Qed.
Lemma lem4454392 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : ((term273 A K s k P f) = (term274 A K s k P f)) = ((term181 A K s k P f) = (term290 A K s k P f)).
Proof. exact (MK_COMB (@lem4454383 A K s k P f) (@lem4454391 A K s k P f)). Qed.
Lemma lem4454393 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term181 A K s k P f) = (term290 A K s k P f).
Proof. exact (EQ_MP (@lem4454392 A K s k P f) (@lem4454370 A K s k P f)). Qed.
Lemma lem4454394 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term192 A K s k P) = (term291 A K s k P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454393 A K s k P f)). Qed.
Lemma lem4454395 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4454396 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term193 A K s k P) = (term292 A K s k P).
Proof. exact (MK_COMB (@lem4454395 A K) (@lem4454394 A K s k P)). Qed.
Lemma lem4454398 {A B : Type'} (P : type1413 A B) : (term293 A B P) = (term294 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4454399 {A K : Type'} (P : type799 A K) : (term295 A K P) = (term296 A K P).
Proof. exact (@lem4454398 (K -> A) K P). Qed.
Lemma lem4454400 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term297 A K s k P) = (term298 A K s k P).
Proof. exact (@lem4454399 A K (term299 A K s k P)). Qed.
Lemma lem4454401 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term300 A K s k P f) = (term289 A K s k P f).
Proof. exact (eq_refl (term300 A K s k P f)). Qed.
Lemma lem4454402 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4454403 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term301 A K s k P f i) = (term302 A K s k P f i).
Proof. exact (MK_COMB (@lem4454401 A K s k P f) (@lem4454402 K i)). Qed.
Lemma lem4454404 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term302 A K s k P f i) = (term287 A K s k P f i).
Proof. exact (eq_refl (term302 A K s k P f i)). Qed.
Lemma lem4454405 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term301 A K s k P f i) = (term287 A K s k P f i).
Proof. exact (TRANS (@lem4454403 A K s k P f i) (@lem4454404 A K s k P f i)). Qed.
Lemma lem4454406 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term303 A K s k P f) = (term289 A K s k P f).
Proof. exact (fun_ext (fun i : K => @lem4454405 A K s k P f i)). Qed.
Lemma lem4454407 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454408 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term304 A K s k P f) = (term290 A K s k P f).
Proof. exact (MK_COMB (@lem4454407 K) (@lem4454406 A K s k P f)). Qed.
Lemma lem4454409 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term305 A K s k P) = (term291 A K s k P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454408 A K s k P f)). Qed.
Lemma lem4454410 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4454411 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term297 A K s k P) = (term292 A K s k P).
Proof. exact (MK_COMB (@lem4454410 A K) (@lem4454409 A K s k P)). Qed.
Lemma lem4454412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454413 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term306 A K s k P) = (term307 A K s k P).
Proof. exact (MK_COMB (@lem4454412) (@lem4454411 A K s k P)). Qed.
Lemma lem4454414 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term300 A K s k P f) = (term289 A K s k P f).
Proof. exact (eq_refl (term300 A K s k P f)). Qed.
Lemma lem4454415 {A K : Type'} (i : type803 A K) (f : K -> A) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem4454416 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) (f : K -> A) : (term308 A K s k P i f) = (term309 A K s k P i f).
Proof. exact (MK_COMB (@lem4454414 A K s k P f) (@lem4454415 A K i f)). Qed.
Lemma lem4454417 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) (f : K -> A) : (term309 A K s k P i f) = (term310 A K s k P i f).
Proof. exact (eq_refl (term309 A K s k P i f)). Qed.
Lemma lem4454418 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) (f : K -> A) : (term308 A K s k P i f) = (term310 A K s k P i f).
Proof. exact (TRANS (@lem4454416 A K s k P i f) (@lem4454417 A K s k P i f)). Qed.
Lemma lem4454419 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) : (term311 A K s k P i) = (term312 A K s k P i).
Proof. exact (fun_ext (fun f : K -> A => @lem4454418 A K s k P i f)). Qed.
Lemma lem4454420 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4454421 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) : (term313 A K s k P i) = (term314 A K s k P i).
Proof. exact (MK_COMB (@lem4454420 A K) (@lem4454419 A K s k P i)). Qed.
Lemma lem4454422 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term315 A K s k P) = (term316 A K s k P).
Proof. exact (fun_ext (fun i : type803 A K => @lem4454421 A K s k P i)). Qed.
Lemma lem4454423 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4454424 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term298 A K s k P) = (term317 A K s k P).
Proof. exact (MK_COMB (@lem4454423 A K) (@lem4454422 A K s k P)). Qed.
Lemma lem4454425 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : ((term297 A K s k P) = (term298 A K s k P)) = ((term292 A K s k P) = (term317 A K s k P)).
Proof. exact (MK_COMB (@lem4454413 A K s k P) (@lem4454424 A K s k P)). Qed.
Lemma lem4454426 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term292 A K s k P) = (term317 A K s k P).
Proof. exact (EQ_MP (@lem4454425 A K s k P) (@lem4454400 A K s k P)). Qed.
Lemma lem4454427 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term193 A K s k P) = (term317 A K s k P).
Proof. exact (TRANS (@lem4454396 A K s k P) (@lem4454426 A K s k P)). Qed.
Lemma lem4454428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454429 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term224 A K s k P) = (term318 A K s k P).
Proof. exact (MK_COMB (@lem4454428) (@lem4454427 A K s k P)). Qed.
Lemma lem4454431 {A : Type'} (P : Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4454432 {A : Type'} (P : Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (@lem4454431 A P Q). Qed.
Lemma lem4454433 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term321 A K k s P i) = (term322 A K k s P i).
Proof. exact (@lem4454432 A (term323 K i k) (term145 A K s P i)). Qed.
Lemma lem4454434 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term203 A K s P i x) = (term144 A K s P i x).
Proof. exact (eq_refl (term203 A K s P i x)). Qed.
Lemma lem4454435 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term324 A K s P i) = (term145 A K s P i).
Proof. exact (fun_ext (fun x : A => @lem4454434 A K s P i x)). Qed.
Lemma lem4454436 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4454437 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term325 A K s P i) = (term146 A K s P i).
Proof. exact (MK_COMB (@lem4454436 A) (@lem4454435 A K s P i)). Qed.
Lemma lem4454438 {K : Type'} (i : K) (k : K -> Prop) : (term212 K i k) = (term212 K i k).
Proof. exact (eq_refl (term212 K i k)). Qed.
Lemma lem4454439 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term321 A K k s P i) = (term213 A K k s P i).
Proof. exact (MK_COMB (@lem4454438 K i k) (@lem4454437 A K s P i)). Qed.
Lemma lem4454440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454441 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term326 A K k s P i) = (term327 A K k s P i).
Proof. exact (MK_COMB (@lem4454440) (@lem4454439 A K k s P i)). Qed.
Lemma lem4454442 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term203 A K s P i x) = (term144 A K s P i x).
Proof. exact (eq_refl (term203 A K s P i x)). Qed.
Lemma lem4454443 {K : Type'} (i : K) (k : K -> Prop) : (term212 K i k) = (term212 K i k).
Proof. exact (eq_refl (term212 K i k)). Qed.
Lemma lem4454444 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term328 A K k s P i x) = (term329 A K k s P i x).
Proof. exact (MK_COMB (@lem4454443 K i k) (@lem4454442 A K s P i x)). Qed.
Lemma lem4454445 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term330 A K k s P i) = (term331 A K k s P i).
Proof. exact (fun_ext (fun x : A => @lem4454444 A K k s P i x)). Qed.
Lemma lem4454446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4454447 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term322 A K k s P i) = (term332 A K k s P i).
Proof. exact (MK_COMB (@lem4454446 A) (@lem4454445 A K k s P i)). Qed.
Lemma lem4454448 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : ((term321 A K k s P i) = (term322 A K k s P i)) = ((term213 A K k s P i) = (term332 A K k s P i)).
Proof. exact (MK_COMB (@lem4454441 A K k s P i) (@lem4454447 A K k s P i)). Qed.
Lemma lem4454449 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term213 A K k s P i) = (term332 A K k s P i).
Proof. exact (EQ_MP (@lem4454448 A K k s P i) (@lem4454433 A K k s P i)). Qed.
Lemma lem4454450 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term221 A K k s P) = (term333 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4454449 A K k s P i)). Qed.
Lemma lem4454451 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4454452 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term222 A K k s P) = (term334 A K k s P).
Proof. exact (MK_COMB (@lem4454451 K) (@lem4454450 A K k s P)). Qed.
Lemma lem4454454 {A B : Type'} (P : type1413 A B) : (term293 A B P) = (term294 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4454455 {A K : Type'} (P : type1470 A K) : (term335 A K P) = (term336 A K P).
Proof. exact (@lem4454454 K A P). Qed.
Lemma lem4454456 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term337 A K k s P) = (term338 A K k s P).
Proof. exact (@lem4454455 A K (term339 A K k s P)). Qed.
Lemma lem4454457 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term340 A K k s P i) = (term331 A K k s P i).
Proof. exact (eq_refl (term340 A K k s P i)). Qed.
Lemma lem4454458 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4454459 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term341 A K k s P i x) = (term342 A K k s P i x).
Proof. exact (MK_COMB (@lem4454457 A K k s P i) (@lem4454458 A x)). Qed.
Lemma lem4454460 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term342 A K k s P i x) = (term329 A K k s P i x).
Proof. exact (eq_refl (term342 A K k s P i x)). Qed.
Lemma lem4454461 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term341 A K k s P i x) = (term329 A K k s P i x).
Proof. exact (TRANS (@lem4454459 A K k s P i x) (@lem4454460 A K k s P i x)). Qed.
Lemma lem4454462 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term343 A K k s P i) = (term331 A K k s P i).
Proof. exact (fun_ext (fun x : A => @lem4454461 A K k s P i x)). Qed.
Lemma lem4454463 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4454464 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term344 A K k s P i) = (term332 A K k s P i).
Proof. exact (MK_COMB (@lem4454463 A) (@lem4454462 A K k s P i)). Qed.
Lemma lem4454465 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term345 A K k s P) = (term333 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4454464 A K k s P i)). Qed.
Lemma lem4454466 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4454467 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term337 A K k s P) = (term334 A K k s P).
Proof. exact (MK_COMB (@lem4454466 K) (@lem4454465 A K k s P)). Qed.
Lemma lem4454468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454469 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term346 A K k s P) = (term347 A K k s P).
Proof. exact (MK_COMB (@lem4454468) (@lem4454467 A K k s P)). Qed.
Lemma lem4454470 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term340 A K k s P i) = (term331 A K k s P i).
Proof. exact (eq_refl (term340 A K k s P i)). Qed.
Lemma lem4454471 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4454472 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (i : K) : (term348 A K k s P x i) = (term349 A K k s P x i).
Proof. exact (MK_COMB (@lem4454470 A K k s P i) (@lem4454471 A K x i)). Qed.
Lemma lem4454473 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (i : K) : (term349 A K k s P x i) = (term350 A K k s P x i).
Proof. exact (eq_refl (term349 A K k s P x i)). Qed.
Lemma lem4454474 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (i : K) : (term348 A K k s P x i) = (term350 A K k s P x i).
Proof. exact (TRANS (@lem4454472 A K k s P x i) (@lem4454473 A K k s P x i)). Qed.
Lemma lem4454475 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term351 A K k s P x) = (term352 A K k s P x).
Proof. exact (fun_ext (fun i : K => @lem4454474 A K k s P x i)). Qed.
Lemma lem4454476 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4454477 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term353 A K k s P x) = (term354 A K k s P x).
Proof. exact (MK_COMB (@lem4454476 K) (@lem4454475 A K k s P x)). Qed.
Lemma lem4454478 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term355 A K k s P) = (term356 A K k s P).
Proof. exact (fun_ext (fun x : K -> A => @lem4454477 A K k s P x)). Qed.
Lemma lem4454479 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454480 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term338 A K k s P) = (term357 A K k s P).
Proof. exact (MK_COMB (@lem4454479 A K) (@lem4454478 A K k s P)). Qed.
Lemma lem4454481 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term337 A K k s P) = (term338 A K k s P)) = ((term334 A K k s P) = (term357 A K k s P)).
Proof. exact (MK_COMB (@lem4454469 A K k s P) (@lem4454480 A K k s P)). Qed.
Lemma lem4454482 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term334 A K k s P) = (term357 A K k s P).
Proof. exact (EQ_MP (@lem4454481 A K k s P) (@lem4454456 A K k s P)). Qed.
Lemma lem4454483 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term222 A K k s P) = (term357 A K k s P).
Proof. exact (TRANS (@lem4454452 A K k s P) (@lem4454482 A K k s P)). Qed.
Lemma lem4454484 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term226 A K k s P) = (term358 A K k s P).
Proof. exact (MK_COMB (@lem4454429 A K s k P) (@lem4454483 A K k s P)). Qed.
Lemma lem4454486 {A : Type'} (P : A -> Prop) (Q : Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4454487 {A K : Type'} (P : type198 A K) (Q : Prop) : (term359 A K P Q) = (term360 A K P Q).
Proof. exact (@lem4454486 (type803 A K) P Q). Qed.
Lemma lem4454488 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term361 A K k s P) = (term362 A K k s P).
Proof. exact (@lem4454487 A K (term316 A K s k P) (term357 A K k s P)). Qed.
Lemma lem4454489 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) : (term363 A K s k P i) = (term314 A K s k P i).
Proof. exact (eq_refl (term363 A K s k P i)). Qed.
Lemma lem4454490 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term364 A K s k P) = (term316 A K s k P).
Proof. exact (fun_ext (fun i : type803 A K => @lem4454489 A K s k P i)). Qed.
Lemma lem4454491 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4454492 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term365 A K s k P) = (term317 A K s k P).
Proof. exact (MK_COMB (@lem4454491 A K) (@lem4454490 A K s k P)). Qed.
Lemma lem4454493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454494 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term366 A K s k P) = (term318 A K s k P).
Proof. exact (MK_COMB (@lem4454493) (@lem4454492 A K s k P)). Qed.
Lemma lem4454495 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term357 A K k s P) = (term357 A K k s P).
Proof. exact (eq_refl (term357 A K k s P)). Qed.
Lemma lem4454496 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term361 A K k s P) = (term358 A K k s P).
Proof. exact (MK_COMB (@lem4454494 A K s k P) (@lem4454495 A K k s P)). Qed.
Lemma lem4454497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454498 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term367 A K k s P) = (term368 A K k s P).
Proof. exact (MK_COMB (@lem4454497) (@lem4454496 A K k s P)). Qed.
Lemma lem4454499 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) : (term363 A K s k P i) = (term314 A K s k P i).
Proof. exact (eq_refl (term363 A K s k P i)). Qed.
Lemma lem4454500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454501 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) : (term369 A K s k P i) = (term370 A K s k P i).
Proof. exact (MK_COMB (@lem4454500) (@lem4454499 A K s k P i)). Qed.
Lemma lem4454502 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term357 A K k s P) = (term357 A K k s P).
Proof. exact (eq_refl (term357 A K k s P)). Qed.
Lemma lem4454503 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term371 A K i k s P) = (term372 A K i k s P).
Proof. exact (MK_COMB (@lem4454501 A K s k P i) (@lem4454502 A K k s P)). Qed.
Lemma lem4454504 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term373 A K k s P) = (term374 A K k s P).
Proof. exact (fun_ext (fun i : type803 A K => @lem4454503 A K i k s P)). Qed.
Lemma lem4454505 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4454506 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term362 A K k s P) = (term375 A K k s P).
Proof. exact (MK_COMB (@lem4454505 A K) (@lem4454504 A K k s P)). Qed.
Lemma lem4454507 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term361 A K k s P) = (term362 A K k s P)) = ((term358 A K k s P) = (term375 A K k s P)).
Proof. exact (MK_COMB (@lem4454498 A K k s P) (@lem4454506 A K k s P)). Qed.
Lemma lem4454508 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term358 A K k s P) = (term375 A K k s P).
Proof. exact (EQ_MP (@lem4454507 A K k s P) (@lem4454488 A K k s P)). Qed.
Lemma lem4454510 {A : Type'} (P : Prop) (Q : A -> Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4454511 {A K : Type'} (P : Prop) (Q : type805 A K) : (term376 A K P Q) = (term377 A K P Q).
Proof. exact (@lem4454510 (K -> A) P Q). Qed.
Lemma lem4454512 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term378 A K i k s P) = (term379 A K i k s P).
Proof. exact (@lem4454511 A K (term314 A K s k P i) (term356 A K k s P)). Qed.
Lemma lem4454513 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term380 A K k s P x) = (term354 A K k s P x).
Proof. exact (eq_refl (term380 A K k s P x)). Qed.
Lemma lem4454514 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term381 A K k s P) = (term356 A K k s P).
Proof. exact (fun_ext (fun x : K -> A => @lem4454513 A K k s P x)). Qed.
Lemma lem4454515 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454516 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term382 A K k s P) = (term357 A K k s P).
Proof. exact (MK_COMB (@lem4454515 A K) (@lem4454514 A K k s P)). Qed.
Lemma lem4454517 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) : (term370 A K s k P i) = (term370 A K s k P i).
Proof. exact (eq_refl (term370 A K s k P i)). Qed.
Lemma lem4454518 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term378 A K i k s P) = (term372 A K i k s P).
Proof. exact (MK_COMB (@lem4454517 A K s k P i) (@lem4454516 A K k s P)). Qed.
Lemma lem4454519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454520 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term383 A K i k s P) = (term384 A K i k s P).
Proof. exact (MK_COMB (@lem4454519) (@lem4454518 A K i k s P)). Qed.
Lemma lem4454521 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term380 A K k s P x) = (term354 A K k s P x).
Proof. exact (eq_refl (term380 A K k s P x)). Qed.
Lemma lem4454522 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i : type803 A K) : (term370 A K s k P i) = (term370 A K s k P i).
Proof. exact (eq_refl (term370 A K s k P i)). Qed.
Lemma lem4454523 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term385 A K i k s P x) = (term386 A K i k s P x).
Proof. exact (MK_COMB (@lem4454522 A K s k P i) (@lem4454521 A K k s P x)). Qed.
Lemma lem4454524 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term387 A K i k s P) = (term388 A K i k s P).
Proof. exact (fun_ext (fun x : K -> A => @lem4454523 A K i k s P x)). Qed.
Lemma lem4454525 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454526 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term379 A K i k s P) = (term389 A K i k s P).
Proof. exact (MK_COMB (@lem4454525 A K) (@lem4454524 A K i k s P)). Qed.
Lemma lem4454527 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term378 A K i k s P) = (term379 A K i k s P)) = ((term372 A K i k s P) = (term389 A K i k s P)).
Proof. exact (MK_COMB (@lem4454520 A K i k s P) (@lem4454526 A K i k s P)). Qed.
Lemma lem4454528 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term372 A K i k s P) = (term389 A K i k s P).
Proof. exact (EQ_MP (@lem4454527 A K i k s P) (@lem4454512 A K i k s P)). Qed.
Lemma lem4454529 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term374 A K k s P) = (term390 A K k s P).
Proof. exact (fun_ext (fun i : type803 A K => @lem4454528 A K i k s P)). Qed.
Lemma lem4454530 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4454531 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term375 A K k s P) = (term391 A K k s P).
Proof. exact (MK_COMB (@lem4454530 A K) (@lem4454529 A K k s P)). Qed.
Lemma lem4454532 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term358 A K k s P) = (term391 A K k s P).
Proof. exact (TRANS (@lem4454508 A K k s P) (@lem4454531 A K k s P)). Qed.
Lemma lem4454533 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term226 A K k s P) = (term391 A K k s P).
Proof. exact (TRANS (@lem4454484 A K k s P) (@lem4454532 A K k s P)). Qed.
Lemma lem4454534 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term234 A K k s P) = (term392 A K k s P).
Proof. exact (MK_COMB (@lem4454366 A K k s P) (@lem4454533 A K k s P)). Qed.
Lemma lem4454538 {A : Type'} (P : A -> Prop) (Q : Prop) : (term393 A P Q) = (term394 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4454539 {A K : Type'} (P : type805 A K) (Q : Prop) : (term395 A K P Q) = (term396 A K P Q).
Proof. exact (@lem4454538 (K -> A) P Q). Qed.
Lemma lem4454540 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term397 A K k s P) = (term398 A K k s P).
Proof. exact (@lem4454539 A K (term268 A K k s P) (term391 A K k s P)). Qed.
Lemma lem4454541 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term399 A K k s P f) = (term267 A K f k s P).
Proof. exact (eq_refl (term399 A K k s P f)). Qed.
Lemma lem4454542 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term400 A K k s P) = (term268 A K k s P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454541 A K f k s P)). Qed.
Lemma lem4454543 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454544 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term401 A K k s P) = (term269 A K k s P).
Proof. exact (MK_COMB (@lem4454543 A K) (@lem4454542 A K k s P)). Qed.
Lemma lem4454545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454546 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term402 A K k s P) = (term270 A K k s P).
Proof. exact (MK_COMB (@lem4454545) (@lem4454544 A K k s P)). Qed.
Lemma lem4454547 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term391 A K k s P) = (term391 A K k s P).
Proof. exact (eq_refl (term391 A K k s P)). Qed.
Lemma lem4454548 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term397 A K k s P) = (term392 A K k s P).
Proof. exact (MK_COMB (@lem4454546 A K k s P) (@lem4454547 A K k s P)). Qed.
Lemma lem4454549 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454550 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term403 A K k s P) = (term404 A K k s P).
Proof. exact (MK_COMB (@lem4454549) (@lem4454548 A K k s P)). Qed.
Lemma lem4454551 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term399 A K k s P f) = (term267 A K f k s P).
Proof. exact (eq_refl (term399 A K k s P f)). Qed.
Lemma lem4454552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454553 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term405 A K k s P f) = (term406 A K f k s P).
Proof. exact (MK_COMB (@lem4454552) (@lem4454551 A K f k s P)). Qed.
Lemma lem4454554 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term391 A K k s P) = (term391 A K k s P).
Proof. exact (eq_refl (term391 A K k s P)). Qed.
Lemma lem4454555 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term407 A K f k s P) = (term408 A K f k s P).
Proof. exact (MK_COMB (@lem4454553 A K f k s P) (@lem4454554 A K k s P)). Qed.
Lemma lem4454556 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term409 A K k s P) = (term410 A K k s P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454555 A K f k s P)). Qed.
Lemma lem4454557 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454558 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term398 A K k s P) = (term411 A K k s P).
Proof. exact (MK_COMB (@lem4454557 A K) (@lem4454556 A K k s P)). Qed.
Lemma lem4454559 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term397 A K k s P) = (term398 A K k s P)) = ((term392 A K k s P) = (term411 A K k s P)).
Proof. exact (MK_COMB (@lem4454550 A K k s P) (@lem4454558 A K k s P)). Qed.
Lemma lem4454560 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term392 A K k s P) = (term411 A K k s P).
Proof. exact (EQ_MP (@lem4454559 A K k s P) (@lem4454540 A K k s P)). Qed.
Lemma lem4454564 {A : Type'} (P : A -> Prop) (Q : Prop) : (term393 A P Q) = (term394 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4454565 {K : Type'} (P : K -> Prop) (Q : Prop) : (term393 K P Q) = (term394 K P Q).
Proof. exact (@lem4454564 K P Q). Qed.
Lemma lem4454566 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term412 A K f k s P) = (term413 A K f k s P).
Proof. exact (@lem4454565 K (term266 A K f k s P) (term391 A K k s P)). Qed.
Lemma lem4454567 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term414 A K f k s P i) = (term264 A K f k s P i).
Proof. exact (eq_refl (term414 A K f k s P i)). Qed.
Lemma lem4454568 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term415 A K f k s P) = (term266 A K f k s P).
Proof. exact (fun_ext (fun i : K => @lem4454567 A K f k s P i)). Qed.
Lemma lem4454569 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454570 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term416 A K f k s P) = (term267 A K f k s P).
Proof. exact (MK_COMB (@lem4454569 K) (@lem4454568 A K f k s P)). Qed.
Lemma lem4454571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454572 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term417 A K f k s P) = (term406 A K f k s P).
Proof. exact (MK_COMB (@lem4454571) (@lem4454570 A K f k s P)). Qed.
Lemma lem4454573 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term391 A K k s P) = (term391 A K k s P).
Proof. exact (eq_refl (term391 A K k s P)). Qed.
Lemma lem4454574 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term412 A K f k s P) = (term408 A K f k s P).
Proof. exact (MK_COMB (@lem4454572 A K f k s P) (@lem4454573 A K k s P)). Qed.
Lemma lem4454575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454576 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term418 A K f k s P) = (term419 A K f k s P).
Proof. exact (MK_COMB (@lem4454575) (@lem4454574 A K f k s P)). Qed.
Lemma lem4454577 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term414 A K f k s P i) = (term264 A K f k s P i).
Proof. exact (eq_refl (term414 A K f k s P i)). Qed.
Lemma lem4454578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454579 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term420 A K f k s P i) = (term421 A K f k s P i).
Proof. exact (MK_COMB (@lem4454578) (@lem4454577 A K f k s P i)). Qed.
Lemma lem4454580 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term391 A K k s P) = (term391 A K k s P).
Proof. exact (eq_refl (term391 A K k s P)). Qed.
Lemma lem4454581 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term422 A K f i k s P) = (term423 A K f i k s P).
Proof. exact (MK_COMB (@lem4454579 A K f k s P i) (@lem4454580 A K k s P)). Qed.
Lemma lem4454582 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term424 A K f k s P) = (term425 A K f k s P).
Proof. exact (fun_ext (fun i : K => @lem4454581 A K f i k s P)). Qed.
Lemma lem4454583 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454584 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term413 A K f k s P) = (term426 A K f k s P).
Proof. exact (MK_COMB (@lem4454583 K) (@lem4454582 A K f k s P)). Qed.
Lemma lem4454585 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term412 A K f k s P) = (term413 A K f k s P)) = ((term408 A K f k s P) = (term426 A K f k s P)).
Proof. exact (MK_COMB (@lem4454576 A K f k s P) (@lem4454584 A K f k s P)). Qed.
Lemma lem4454586 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term408 A K f k s P) = (term426 A K f k s P).
Proof. exact (EQ_MP (@lem4454585 A K f k s P) (@lem4454566 A K f k s P)). Qed.
Lemma lem4454588 {A : Type'} (P : Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4454589 {A K : Type'} (P : Prop) (Q : type198 A K) : (term427 A K P Q) = (term428 A K P Q).
Proof. exact (@lem4454588 (type803 A K) P Q). Qed.
Lemma lem4454590 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term429 A K f i k s P) = (term430 A K f i k s P).
Proof. exact (@lem4454589 A K (term264 A K f k s P i) (term390 A K k s P)). Qed.
Lemma lem4454591 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term431 A K k s P i) = (term389 A K i k s P).
Proof. exact (eq_refl (term431 A K k s P i)). Qed.
Lemma lem4454592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term432 A K k s P) = (term390 A K k s P).
Proof. exact (fun_ext (fun i : type803 A K => @lem4454591 A K i k s P)). Qed.
Lemma lem4454593 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4454594 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term433 A K k s P) = (term391 A K k s P).
Proof. exact (MK_COMB (@lem4454593 A K) (@lem4454592 A K k s P)). Qed.
Lemma lem4454595 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term421 A K f k s P i) = (term421 A K f k s P i).
Proof. exact (eq_refl (term421 A K f k s P i)). Qed.
Lemma lem4454596 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term429 A K f i k s P) = (term423 A K f i k s P).
Proof. exact (MK_COMB (@lem4454595 A K f k s P i) (@lem4454594 A K k s P)). Qed.
Lemma lem4454597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454598 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term434 A K f i k s P) = (term435 A K f i k s P).
Proof. exact (MK_COMB (@lem4454597) (@lem4454596 A K f i k s P)). Qed.
Lemma lem4454599 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term431 A K k s P i) = (term389 A K i k s P).
Proof. exact (eq_refl (term431 A K k s P i)). Qed.
Lemma lem4454600 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term421 A K f k s P i) = (term421 A K f k s P i).
Proof. exact (eq_refl (term421 A K f k s P i)). Qed.
Lemma lem4454601 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term436 A K f i k s P i') = (term437 A K f i i' k s P).
Proof. exact (MK_COMB (@lem4454600 A K f k s P i) (@lem4454599 A K i' k s P)). Qed.
Lemma lem4454602 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term438 A K f i k s P) = (term439 A K f i k s P).
Proof. exact (fun_ext (fun i' : type803 A K => @lem4454601 A K f i i' k s P)). Qed.
Lemma lem4454603 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4454604 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term430 A K f i k s P) = (term440 A K f i k s P).
Proof. exact (MK_COMB (@lem4454603 A K) (@lem4454602 A K f i k s P)). Qed.
Lemma lem4454605 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term429 A K f i k s P) = (term430 A K f i k s P)) = ((term423 A K f i k s P) = (term440 A K f i k s P)).
Proof. exact (MK_COMB (@lem4454598 A K f i k s P) (@lem4454604 A K f i k s P)). Qed.
Lemma lem4454606 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term423 A K f i k s P) = (term440 A K f i k s P).
Proof. exact (EQ_MP (@lem4454605 A K f i k s P) (@lem4454590 A K f i k s P)). Qed.
Lemma lem4454608 {A : Type'} (P : Prop) (Q : A -> Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4454609 {A K : Type'} (P : Prop) (Q : type805 A K) : (term441 A K P Q) = (term442 A K P Q).
Proof. exact (@lem4454608 (K -> A) P Q). Qed.
Lemma lem4454610 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term443 A K f i i' k s P) = (term444 A K f i i' k s P).
Proof. exact (@lem4454609 A K (term264 A K f k s P i) (term388 A K i' k s P)). Qed.
Lemma lem4454611 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term445 A K i k s P x) = (term386 A K i k s P x).
Proof. exact (eq_refl (term445 A K i k s P x)). Qed.
Lemma lem4454612 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term446 A K i k s P) = (term388 A K i k s P).
Proof. exact (fun_ext (fun x : K -> A => @lem4454611 A K i k s P x)). Qed.
Lemma lem4454613 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454614 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term447 A K i k s P) = (term389 A K i k s P).
Proof. exact (MK_COMB (@lem4454613 A K) (@lem4454612 A K i k s P)). Qed.
Lemma lem4454615 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term421 A K f k s P i) = (term421 A K f k s P i).
Proof. exact (eq_refl (term421 A K f k s P i)). Qed.
Lemma lem4454616 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term443 A K f i i' k s P) = (term437 A K f i i' k s P).
Proof. exact (MK_COMB (@lem4454615 A K f k s P i) (@lem4454614 A K i' k s P)). Qed.
Lemma lem4454617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4454618 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term448 A K f i i' k s P) = (term449 A K f i i' k s P).
Proof. exact (MK_COMB (@lem4454617) (@lem4454616 A K f i i' k s P)). Qed.
Lemma lem4454619 {A K : Type'} (i : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term445 A K i k s P x) = (term386 A K i k s P x).
Proof. exact (eq_refl (term445 A K i k s P x)). Qed.
Lemma lem4454620 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term421 A K f k s P i) = (term421 A K f k s P i).
Proof. exact (eq_refl (term421 A K f k s P i)). Qed.
Lemma lem4454621 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term450 A K f i i' k s P x) = (term451 A K f i i' k s P x).
Proof. exact (MK_COMB (@lem4454620 A K f k s P i) (@lem4454619 A K i' k s P x)). Qed.
Lemma lem4454622 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term452 A K f i i' k s P) = (term453 A K f i i' k s P).
Proof. exact (fun_ext (fun x : K -> A => @lem4454621 A K f i i' k s P x)). Qed.
Lemma lem4454623 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454624 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term444 A K f i i' k s P) = (term454 A K f i i' k s P).
Proof. exact (MK_COMB (@lem4454623 A K) (@lem4454622 A K f i i' k s P)). Qed.
Lemma lem4454625 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term443 A K f i i' k s P) = (term444 A K f i i' k s P)) = ((term437 A K f i i' k s P) = (term454 A K f i i' k s P)).
Proof. exact (MK_COMB (@lem4454618 A K f i i' k s P) (@lem4454624 A K f i i' k s P)). Qed.
Lemma lem4454626 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term437 A K f i i' k s P) = (term454 A K f i i' k s P).
Proof. exact (EQ_MP (@lem4454625 A K f i i' k s P) (@lem4454610 A K f i i' k s P)). Qed.
Lemma lem4454627 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term439 A K f i k s P) = (term455 A K f i k s P).
Proof. exact (fun_ext (fun i' : type803 A K => @lem4454626 A K f i i' k s P)). Qed.
Lemma lem4454628 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4454629 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term440 A K f i k s P) = (term456 A K f i k s P).
Proof. exact (MK_COMB (@lem4454628 A K) (@lem4454627 A K f i k s P)). Qed.
Lemma lem4454630 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term423 A K f i k s P) = (term456 A K f i k s P).
Proof. exact (TRANS (@lem4454606 A K f i k s P) (@lem4454629 A K f i k s P)). Qed.
Lemma lem4454631 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term425 A K f k s P) = (term457 A K f k s P).
Proof. exact (fun_ext (fun i : K => @lem4454630 A K f i k s P)). Qed.
Lemma lem4454632 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4454633 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term426 A K f k s P) = (term458 A K f k s P).
Proof. exact (MK_COMB (@lem4454632 K) (@lem4454631 A K f k s P)). Qed.
Lemma lem4454634 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term408 A K f k s P) = (term458 A K f k s P).
Proof. exact (TRANS (@lem4454586 A K f k s P) (@lem4454633 A K f k s P)). Qed.
Lemma lem4454635 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term410 A K k s P) = (term459 A K k s P).
Proof. exact (fun_ext (fun f : K -> A => @lem4454634 A K f k s P)). Qed.
Lemma lem4454636 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4454637 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term411 A K k s P) = (term460 A K k s P).
Proof. exact (MK_COMB (@lem4454636 A K) (@lem4454635 A K k s P)). Qed.
Lemma lem4454638 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term392 A K k s P) = (term460 A K k s P).
Proof. exact (TRANS (@lem4454560 A K k s P) (@lem4454637 A K k s P)). Qed.
Lemma lem4454640 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term234 A K k s P) = (term460 A K k s P).
Proof. exact (TRANS (@lem4454534 A K k s P) (@lem4454638 A K k s P)). Qed.
Lemma lem4454641 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term126 A K k s P) = (term460 A K k s P).
Proof. exact (TRANS (@lem4453835 A K k s P) (@lem4454640 A K k s P)). Qed.
Lemma lem4454642 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : term460 A K k s P.
Proof. exact (EQ_MP (@lem4454641 A K k s P) (@lem4453699 A K k s P h1)). Qed.
Lemma lem4454643 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term458 A K f k s P) : term458 A K f k s P.
Proof. exact (h1). Qed.
Lemma lem4454644 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term456 A K f i k s P) : term456 A K f i k s P.
Proof. exact (h1). Qed.
Lemma lem4454645 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term454 A K f i i' k s P) : term454 A K f i i' k s P.
Proof. exact (h1). Qed.
Lemma lem4454646 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term451 A K f i i' k s P x) : term451 A K f i i' k s P x.
Proof. exact (h1). Qed.
Lemma lem4454653 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454654 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4454653 K A f x). Qed.
Lemma lem4454656 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4454654 A K x i). Qed.
Lemma lem4454657 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem4454658 {A K : Type'} (P : type1470 A K) (x : K -> A) (i : K) : (term115 A K P x i) = (term461 A K P x i).
Proof. exact (MK_COMB (@lem4454657 A K P i) (@lem4454656 A K x i)). Qed.
Lemma lem4454660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454661 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4454660 K (A -> Prop) f x). Qed.
Lemma lem4454662 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (@I (K -> A -> Prop) P i).
Proof. exact (@lem4454661 A K P i). Qed.
Lemma lem4454663 {A K : Type'} (x : K -> A) (i : K) : (@I (K -> A) x i) = (@I (K -> A) x i).
Proof. exact (eq_refl (@I (K -> A) x i)). Qed.
Lemma lem4454664 {A K : Type'} (P : type1470 A K) (x : K -> A) (i : K) : (term461 A K P x i) = (term462 A K P x i).
Proof. exact (MK_COMB (@lem4454662 A K P i) (@lem4454663 A K x i)). Qed.
Lemma lem4454666 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454667 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4454666 A Prop f x). Qed.
Lemma lem4454668 {A K : Type'} (P : type1470 A K) (x : K -> A) (i : K) : (term462 A K P x i) = (term463 A K P x i).
Proof. exact (@lem4454667 A (@I (K -> A -> Prop) P i) (@I (K -> A) x i)). Qed.
Lemma lem4454669 {A K : Type'} (P : type1470 A K) (x : K -> A) (i : K) : (term461 A K P x i) = (term463 A K P x i).
Proof. exact (TRANS (@lem4454664 A K P x i) (@lem4454668 A K P x i)). Qed.
Lemma lem4454670 {A K : Type'} (P : type1470 A K) (x : K -> A) (i : K) : (term115 A K P x i) = (term463 A K P x i).
Proof. exact (TRANS (@lem4454658 A K P x i) (@lem4454669 A K P x i)). Qed.
Lemma lem4454671 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4454676 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454677 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4454676 K A f x). Qed.
Lemma lem4454679 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4454677 A K x i). Qed.
Lemma lem4454684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454685 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4454684 K (A -> Prop) f x). Qed.
Lemma lem4454687 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4454685 A K s i). Qed.
Lemma lem4454688 {A K : Type'} (x : K -> A) (i : K) : (term464 A K x i) = (term465 A K x i).
Proof. exact (MK_COMB (@lem4454671 A) (@lem4454679 A K x i)). Qed.
Lemma lem4454689 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term153 A K x s i) = (term466 A K x s i).
Proof. exact (MK_COMB (@lem4454688 A K x i) (@lem4454687 A K s i)). Qed.
Lemma lem4454691 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454692 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4454691 A (type686 A) f x). Qed.
Lemma lem4454693 {A K : Type'} (x : K -> A) (i : K) : (term465 A K x i) = (term467 A K x i).
Proof. exact (@lem4454692 A (@IN A) (@I (K -> A) x i)). Qed.
Lemma lem4454694 {A K : Type'} (s : type1470 A K) (i : K) : (@I (K -> A -> Prop) s i) = (@I (K -> A -> Prop) s i).
Proof. exact (eq_refl (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4454695 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term466 A K x s i) = (term468 A K x s i).
Proof. exact (MK_COMB (@lem4454693 A K x i) (@lem4454694 A K s i)). Qed.
Lemma lem4454697 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454698 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4454697 (A -> Prop) Prop f x). Qed.
Lemma lem4454699 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term468 A K x s i) = (term469 A K x s i).
Proof. exact (@lem4454698 A (term467 A K x i) (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4454700 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term466 A K x s i) = (term469 A K x s i).
Proof. exact (TRANS (@lem4454695 A K x s i) (@lem4454699 A K x s i)). Qed.
Lemma lem4454701 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term153 A K x s i) = (term469 A K x s i).
Proof. exact (TRANS (@lem4454689 A K x s i) (@lem4454700 A K x s i)). Qed.
Lemma lem4454702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454703 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term470 A K x s i) = (term471 A K x s i).
Proof. exact (MK_COMB (@lem4454702) (@lem4454701 A K x s i)). Qed.
Lemma lem4454704 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (x : K -> A) (i : K) : (term472 A K s P x i) = (term473 A K s P x i).
Proof. exact (MK_COMB (@lem4454703 A K x s i) (@lem4454670 A K P x i)). Qed.
Lemma lem4454705 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4454712 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454713 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4454712 K (type686 K) f x). Qed.
Lemma lem4454714 {K : Type'} (i : K) : (@IN K i) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i).
Proof. exact (@lem4454713 K (@IN K) i). Qed.
Lemma lem4454715 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4454716 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i k).
Proof. exact (MK_COMB (@lem4454714 K i) (@lem4454715 K k)). Qed.
Lemma lem4454718 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454719 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4454718 (K -> Prop) Prop f x). Qed.
Lemma lem4454720 {K : Type'} (i : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) i k) = (term474 K i k).
Proof. exact (@lem4454719 K (@I (K -> (K -> Prop) -> Prop) (@IN K) i) k). Qed.
Lemma lem4454722 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (term474 K i k).
Proof. exact (TRANS (@lem4454716 K i k) (@lem4454720 K i k)). Qed.
Lemma lem4454723 {K : Type'} (i : K) (k : K -> Prop) : (term323 K i k) = (term475 K i k).
Proof. exact (MK_COMB (@lem4454705) (@lem4454722 K i k)). Qed.
Lemma lem4454724 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454725 {K : Type'} (i : K) (k : K -> Prop) : (term212 K i k) = (term476 K i k).
Proof. exact (MK_COMB (@lem4454724) (@lem4454723 K i k)). Qed.
Lemma lem4454726 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (i : K) : (term350 A K k s P x i) = (term477 A K k s P x i).
Proof. exact (MK_COMB (@lem4454725 K i k) (@lem4454704 A K s P x i)). Qed.
Lemma lem4454727 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term352 A K k s P x) = (term478 A K k s P x).
Proof. exact (fun_ext (fun i : K => @lem4454726 A K k s P x i)). Qed.
Lemma lem4454728 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4454729 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term354 A K k s P x) = (term479 A K k s P x).
Proof. exact (MK_COMB (@lem4454728 K) (@lem4454727 A K k s P x)). Qed.
Lemma lem4454730 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4454731 {A K : Type'} (P : type1470 A K) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4454736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454737 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4454736 (K -> A) K f x). Qed.
Lemma lem4454739 {A K : Type'} (i' : type803 A K) (f : K -> A) : (i' f) = (@I ((K -> A) -> K) i' f).
Proof. exact (@lem4454737 A K i' f). Qed.
Lemma lem4454740 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4454745 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454746 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4454745 (K -> A) K f x). Qed.
Lemma lem4454748 {A K : Type'} (i' : type803 A K) (f : K -> A) : (i' f) = (@I ((K -> A) -> K) i' f).
Proof. exact (@lem4454746 A K i' f). Qed.
Lemma lem4454749 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term480 A K i' f) = (term481 A K i' f).
Proof. exact (MK_COMB (@lem4454740 A K f) (@lem4454748 A K i' f)). Qed.
Lemma lem4454751 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454752 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4454751 K A f x). Qed.
Lemma lem4454753 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term481 A K i' f) = (term482 A K i' f).
Proof. exact (@lem4454752 A K f (@I ((K -> A) -> K) i' f)). Qed.
Lemma lem4454754 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term480 A K i' f) = (term482 A K i' f).
Proof. exact (TRANS (@lem4454749 A K i' f) (@lem4454753 A K i' f)). Qed.
Lemma lem4454755 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term483 A K P i' f) = (term484 A K P i' f).
Proof. exact (MK_COMB (@lem4454731 A K P) (@lem4454739 A K i' f)). Qed.
Lemma lem4454756 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term485 A K P i' f) = (term486 A K P i' f).
Proof. exact (MK_COMB (@lem4454755 A K P i' f) (@lem4454754 A K i' f)). Qed.
Lemma lem4454758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454759 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4454758 K (A -> Prop) f x). Qed.
Lemma lem4454760 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term484 A K P i' f) = (term487 A K P i' f).
Proof. exact (@lem4454759 A K P (@I ((K -> A) -> K) i' f)). Qed.
Lemma lem4454761 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term482 A K i' f) = (term482 A K i' f).
Proof. exact (eq_refl (term482 A K i' f)). Qed.
Lemma lem4454762 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term486 A K P i' f) = (term488 A K P i' f).
Proof. exact (MK_COMB (@lem4454760 A K P i' f) (@lem4454761 A K i' f)). Qed.
Lemma lem4454764 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454765 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4454764 A Prop f x). Qed.
Lemma lem4454766 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term488 A K P i' f) = (term489 A K P i' f).
Proof. exact (@lem4454765 A (term487 A K P i' f) (term482 A K i' f)). Qed.
Lemma lem4454767 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term486 A K P i' f) = (term489 A K P i' f).
Proof. exact (TRANS (@lem4454762 A K P i' f) (@lem4454766 A K P i' f)). Qed.
Lemma lem4454768 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term485 A K P i' f) = (term489 A K P i' f).
Proof. exact (TRANS (@lem4454756 A K P i' f) (@lem4454767 A K P i' f)). Qed.
Lemma lem4454769 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term490 A K P i' f) = (term491 A K P i' f).
Proof. exact (MK_COMB (@lem4454730) (@lem4454768 A K P i' f)). Qed.
Lemma lem4454770 {K : Type'} : (@IN K) = (@IN K).
Proof. exact (eq_refl (@IN K)). Qed.
Lemma lem4454775 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454776 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4454775 (K -> A) K f x). Qed.
Lemma lem4454778 {A K : Type'} (i' : type803 A K) (f : K -> A) : (i' f) = (@I ((K -> A) -> K) i' f).
Proof. exact (@lem4454776 A K i' f). Qed.
Lemma lem4454779 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4454780 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term492 A K i' f) = (term493 A K i' f).
Proof. exact (MK_COMB (@lem4454770 K) (@lem4454778 A K i' f)). Qed.
Lemma lem4454781 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term494 A K i' f k) = (term495 A K i' f k).
Proof. exact (MK_COMB (@lem4454780 A K i' f) (@lem4454779 K k)). Qed.
Lemma lem4454783 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454784 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4454783 K (type686 K) f x). Qed.
Lemma lem4454785 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term493 A K i' f) = (term496 A K i' f).
Proof. exact (@lem4454784 K (@IN K) (@I ((K -> A) -> K) i' f)). Qed.
Lemma lem4454786 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4454787 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term495 A K i' f k) = (term497 A K i' f k).
Proof. exact (MK_COMB (@lem4454785 A K i' f) (@lem4454786 K k)). Qed.
Lemma lem4454789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454790 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4454789 (K -> Prop) Prop f x). Qed.
Lemma lem4454791 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term497 A K i' f k) = (term498 A K i' f k).
Proof. exact (@lem4454790 K (term496 A K i' f) k). Qed.
Lemma lem4454792 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term495 A K i' f k) = (term498 A K i' f k).
Proof. exact (TRANS (@lem4454787 A K i' f k) (@lem4454791 A K i' f k)). Qed.
Lemma lem4454793 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term494 A K i' f k) = (term498 A K i' f k).
Proof. exact (TRANS (@lem4454781 A K i' f k) (@lem4454792 A K i' f k)). Qed.
Lemma lem4454794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454795 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term499 A K i' f k) = (term500 A K i' f k).
Proof. exact (MK_COMB (@lem4454794) (@lem4454793 A K i' f k)). Qed.
Lemma lem4454796 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term501 A K k P i' f) = (term502 A K k P i' f).
Proof. exact (MK_COMB (@lem4454795 A K i' f k) (@lem4454769 A K P i' f)). Qed.
Lemma lem4454797 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4454798 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4454799 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4454804 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454805 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4454804 (K -> A) K f x). Qed.
Lemma lem4454807 {A K : Type'} (i' : type803 A K) (f : K -> A) : (i' f) = (@I ((K -> A) -> K) i' f).
Proof. exact (@lem4454805 A K i' f). Qed.
Lemma lem4454808 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term480 A K i' f) = (term481 A K i' f).
Proof. exact (MK_COMB (@lem4454799 A K f) (@lem4454807 A K i' f)). Qed.
Lemma lem4454810 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454811 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4454810 K A f x). Qed.
Lemma lem4454812 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term481 A K i' f) = (term482 A K i' f).
Proof. exact (@lem4454811 A K f (@I ((K -> A) -> K) i' f)). Qed.
Lemma lem4454813 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term480 A K i' f) = (term482 A K i' f).
Proof. exact (TRANS (@lem4454808 A K i' f) (@lem4454812 A K i' f)). Qed.
Lemma lem4454814 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4454819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454820 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4454819 (K -> A) K f x). Qed.
Lemma lem4454822 {A K : Type'} (i' : type803 A K) (f : K -> A) : (i' f) = (@I ((K -> A) -> K) i' f).
Proof. exact (@lem4454820 A K i' f). Qed.
Lemma lem4454823 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term483 A K s i' f) = (term484 A K s i' f).
Proof. exact (MK_COMB (@lem4454814 A K s) (@lem4454822 A K i' f)). Qed.
Lemma lem4454825 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454826 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4454825 K (A -> Prop) f x). Qed.
Lemma lem4454827 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term484 A K s i' f) = (term487 A K s i' f).
Proof. exact (@lem4454826 A K s (@I ((K -> A) -> K) i' f)). Qed.
Lemma lem4454828 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term483 A K s i' f) = (term487 A K s i' f).
Proof. exact (TRANS (@lem4454823 A K s i' f) (@lem4454827 A K s i' f)). Qed.
Lemma lem4454829 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term503 A K i' f) = (term504 A K i' f).
Proof. exact (MK_COMB (@lem4454798 A) (@lem4454813 A K i' f)). Qed.
Lemma lem4454830 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term505 A K s i' f) = (term506 A K s i' f).
Proof. exact (MK_COMB (@lem4454829 A K i' f) (@lem4454828 A K s i' f)). Qed.
Lemma lem4454832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454833 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4454832 A (type686 A) f x). Qed.
Lemma lem4454834 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term504 A K i' f) = (term507 A K i' f).
Proof. exact (@lem4454833 A (@IN A) (term482 A K i' f)). Qed.
Lemma lem4454835 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term487 A K s i' f) = (term487 A K s i' f).
Proof. exact (eq_refl (term487 A K s i' f)). Qed.
Lemma lem4454836 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term506 A K s i' f) = (term508 A K s i' f).
Proof. exact (MK_COMB (@lem4454834 A K i' f) (@lem4454835 A K s i' f)). Qed.
Lemma lem4454838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454839 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4454838 (A -> Prop) Prop f x). Qed.
Lemma lem4454840 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term508 A K s i' f) = (term509 A K s i' f).
Proof. exact (@lem4454839 A (term507 A K i' f) (term487 A K s i' f)). Qed.
Lemma lem4454841 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term506 A K s i' f) = (term509 A K s i' f).
Proof. exact (TRANS (@lem4454836 A K s i' f) (@lem4454840 A K s i' f)). Qed.
Lemma lem4454842 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term505 A K s i' f) = (term509 A K s i' f).
Proof. exact (TRANS (@lem4454830 A K s i' f) (@lem4454841 A K s i' f)). Qed.
Lemma lem4454843 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term510 A K s i' f) = (term511 A K s i' f).
Proof. exact (MK_COMB (@lem4454797) (@lem4454842 A K s i' f)). Qed.
Lemma lem4454844 {K : Type'} : (@IN K) = (@IN K).
Proof. exact (eq_refl (@IN K)). Qed.
Lemma lem4454849 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454850 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4454849 (K -> A) K f x). Qed.
Lemma lem4454852 {A K : Type'} (i' : type803 A K) (f : K -> A) : (i' f) = (@I ((K -> A) -> K) i' f).
Proof. exact (@lem4454850 A K i' f). Qed.
Lemma lem4454853 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4454854 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term492 A K i' f) = (term493 A K i' f).
Proof. exact (MK_COMB (@lem4454844 K) (@lem4454852 A K i' f)). Qed.
Lemma lem4454855 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term494 A K i' f k) = (term495 A K i' f k).
Proof. exact (MK_COMB (@lem4454854 A K i' f) (@lem4454853 K k)). Qed.
Lemma lem4454857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454858 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4454857 K (type686 K) f x). Qed.
Lemma lem4454859 {A K : Type'} (i' : type803 A K) (f : K -> A) : (term493 A K i' f) = (term496 A K i' f).
Proof. exact (@lem4454858 K (@IN K) (@I ((K -> A) -> K) i' f)). Qed.
Lemma lem4454860 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4454861 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term495 A K i' f k) = (term497 A K i' f k).
Proof. exact (MK_COMB (@lem4454859 A K i' f) (@lem4454860 K k)). Qed.
Lemma lem4454863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454864 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4454863 (K -> Prop) Prop f x). Qed.
Lemma lem4454865 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term497 A K i' f k) = (term498 A K i' f k).
Proof. exact (@lem4454864 K (term496 A K i' f) k). Qed.
Lemma lem4454866 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term495 A K i' f k) = (term498 A K i' f k).
Proof. exact (TRANS (@lem4454861 A K i' f k) (@lem4454865 A K i' f k)). Qed.
Lemma lem4454867 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term494 A K i' f k) = (term498 A K i' f k).
Proof. exact (TRANS (@lem4454855 A K i' f k) (@lem4454866 A K i' f k)). Qed.
Lemma lem4454868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454869 {A K : Type'} (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term499 A K i' f k) = (term500 A K i' f k).
Proof. exact (MK_COMB (@lem4454868) (@lem4454867 A K i' f k)). Qed.
Lemma lem4454870 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term512 A K k s i' f) = (term513 A K k s i' f).
Proof. exact (MK_COMB (@lem4454869 A K i' f k) (@lem4454843 A K s i' f)). Qed.
Lemma lem4454871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454872 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i' : type803 A K) (f : K -> A) : (term514 A K k s i' f) = (term515 A K k s i' f).
Proof. exact (MK_COMB (@lem4454871) (@lem4454870 A K k s i' f)). Qed.
Lemma lem4454873 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term310 A K s k P i' f) = (term516 A K s k P i' f).
Proof. exact (MK_COMB (@lem4454872 A K k s i' f) (@lem4454796 A K k P i' f)). Qed.
Lemma lem4454874 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i' : type803 A K) : (term312 A K s k P i') = (term517 A K s k P i').
Proof. exact (fun_ext (fun f : K -> A => @lem4454873 A K s k P i' f)). Qed.
Lemma lem4454875 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4454876 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i' : type803 A K) : (term314 A K s k P i') = (term518 A K s k P i').
Proof. exact (MK_COMB (@lem4454875 A K) (@lem4454874 A K s k P i')). Qed.
Lemma lem4454877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454878 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (i' : type803 A K) : (term370 A K s k P i') = (term519 A K s k P i').
Proof. exact (MK_COMB (@lem4454877) (@lem4454876 A K s k P i')). Qed.
Lemma lem4454879 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term386 A K i' k s P x) = (term520 A K i' k s P x).
Proof. exact (MK_COMB (@lem4454878 A K s k P i') (@lem4454729 A K k s P x)). Qed.
Lemma lem4454880 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4454887 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454888 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4454887 K (A -> Prop) f x). Qed.
Lemma lem4454889 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (@I (K -> A -> Prop) P i).
Proof. exact (@lem4454888 A K P i). Qed.
Lemma lem4454890 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4454891 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (@I (K -> A -> Prop) P i x).
Proof. exact (MK_COMB (@lem4454889 A K P i) (@lem4454890 A x)). Qed.
Lemma lem4454893 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454894 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4454893 A Prop f x). Qed.
Lemma lem4454895 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (@I (K -> A -> Prop) P i x) = (term521 A K P i x).
Proof. exact (@lem4454894 A (@I (K -> A -> Prop) P i) x). Qed.
Lemma lem4454897 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (term521 A K P i x).
Proof. exact (TRANS (@lem4454891 A K P i x) (@lem4454895 A K P i x)). Qed.
Lemma lem4454898 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term522 A K P i x) = (term523 A K P i x).
Proof. exact (MK_COMB (@lem4454880) (@lem4454897 A K P i x)). Qed.
Lemma lem4454899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4454906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454907 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4454906 K (A -> Prop) f x). Qed.
Lemma lem4454909 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4454907 A K s i). Qed.
Lemma lem4454910 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4454911 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term198 A K x s i) = (term524 A K x s i).
Proof. exact (MK_COMB (@lem4454910 A x) (@lem4454909 A K s i)). Qed.
Lemma lem4454913 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454914 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4454913 A (type686 A) f x). Qed.
Lemma lem4454915 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4454914 A (@IN A) x). Qed.
Lemma lem4454916 {A K : Type'} (s : type1470 A K) (i : K) : (@I (K -> A -> Prop) s i) = (@I (K -> A -> Prop) s i).
Proof. exact (eq_refl (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4454917 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term524 A K x s i) = (term525 A K x s i).
Proof. exact (MK_COMB (@lem4454915 A x) (@lem4454916 A K s i)). Qed.
Lemma lem4454919 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454920 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4454919 (A -> Prop) Prop f x). Qed.
Lemma lem4454921 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term525 A K x s i) = (term526 A K x s i).
Proof. exact (@lem4454920 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4454922 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term524 A K x s i) = (term526 A K x s i).
Proof. exact (TRANS (@lem4454917 A K x s i) (@lem4454921 A K x s i)). Qed.
Lemma lem4454923 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term198 A K x s i) = (term526 A K x s i).
Proof. exact (TRANS (@lem4454911 A K x s i) (@lem4454922 A K x s i)). Qed.
Lemma lem4454924 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term527 A K x s i) = (term528 A K x s i).
Proof. exact (MK_COMB (@lem4454899) (@lem4454923 A K x s i)). Qed.
Lemma lem4454925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454926 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term529 A K x s i) = (term530 A K x s i).
Proof. exact (MK_COMB (@lem4454925) (@lem4454924 A K x s i)). Qed.
Lemma lem4454927 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term197 A K s P i x) = (term531 A K s P i x).
Proof. exact (MK_COMB (@lem4454926 A K x s i) (@lem4454898 A K P i x)). Qed.
Lemma lem4454928 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term206 A K s P i) = (term532 A K s P i).
Proof. exact (fun_ext (fun x : A => @lem4454927 A K s P i x)). Qed.
Lemma lem4454929 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4454930 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term207 A K s P i) = (term533 A K s P i).
Proof. exact (MK_COMB (@lem4454929 A) (@lem4454928 A K s P i)). Qed.
Lemma lem4454937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454938 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4454937 K (type686 K) f x). Qed.
Lemma lem4454939 {K : Type'} (i : K) : (@IN K i) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i).
Proof. exact (@lem4454938 K (@IN K) i). Qed.
Lemma lem4454940 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4454941 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i k).
Proof. exact (MK_COMB (@lem4454939 K i) (@lem4454940 K k)). Qed.
Lemma lem4454943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454944 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4454943 (K -> Prop) Prop f x). Qed.
Lemma lem4454945 {K : Type'} (i : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) i k) = (term474 K i k).
Proof. exact (@lem4454944 K (@I (K -> (K -> Prop) -> Prop) (@IN K) i) k). Qed.
Lemma lem4454947 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (term474 K i k).
Proof. exact (TRANS (@lem4454941 K i k) (@lem4454945 K i k)). Qed.
Lemma lem4454948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4454949 {K : Type'} (i : K) (k : K -> Prop) : (term208 K i k) = (term534 K i k).
Proof. exact (MK_COMB (@lem4454948) (@lem4454947 K i k)). Qed.
Lemma lem4454950 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term210 A K k s P i) = (term535 A K k s P i).
Proof. exact (MK_COMB (@lem4454949 K i k) (@lem4454930 A K s P i)). Qed.
Lemma lem4454957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454958 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4454957 K A f x). Qed.
Lemma lem4454960 {A K : Type'} (f : K -> A) (i : K) : (f i) = (@I (K -> A) f i).
Proof. exact (@lem4454958 A K f i). Qed.
Lemma lem4454961 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem4454962 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) : (term115 A K P f i) = (term461 A K P f i).
Proof. exact (MK_COMB (@lem4454961 A K P i) (@lem4454960 A K f i)). Qed.
Lemma lem4454964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454965 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4454964 K (A -> Prop) f x). Qed.
Lemma lem4454966 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (@I (K -> A -> Prop) P i).
Proof. exact (@lem4454965 A K P i). Qed.
Lemma lem4454967 {A K : Type'} (f : K -> A) (i : K) : (@I (K -> A) f i) = (@I (K -> A) f i).
Proof. exact (eq_refl (@I (K -> A) f i)). Qed.
Lemma lem4454968 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) : (term461 A K P f i) = (term462 A K P f i).
Proof. exact (MK_COMB (@lem4454966 A K P i) (@lem4454967 A K f i)). Qed.
Lemma lem4454970 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454971 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4454970 A Prop f x). Qed.
Lemma lem4454972 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) : (term462 A K P f i) = (term463 A K P f i).
Proof. exact (@lem4454971 A (@I (K -> A -> Prop) P i) (@I (K -> A) f i)). Qed.
Lemma lem4454973 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) : (term461 A K P f i) = (term463 A K P f i).
Proof. exact (TRANS (@lem4454968 A K P f i) (@lem4454972 A K P f i)). Qed.
Lemma lem4454974 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) : (term115 A K P f i) = (term463 A K P f i).
Proof. exact (TRANS (@lem4454962 A K P f i) (@lem4454973 A K P f i)). Qed.
Lemma lem4454975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4454982 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454983 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4454982 K (type686 K) f x). Qed.
Lemma lem4454984 {K : Type'} (i : K) : (@IN K i) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i).
Proof. exact (@lem4454983 K (@IN K) i). Qed.
Lemma lem4454985 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4454986 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i k).
Proof. exact (MK_COMB (@lem4454984 K i) (@lem4454985 K k)). Qed.
Lemma lem4454988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4454989 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4454988 (K -> Prop) Prop f x). Qed.
Lemma lem4454990 {K : Type'} (i : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) i k) = (term474 K i k).
Proof. exact (@lem4454989 K (@I (K -> (K -> Prop) -> Prop) (@IN K) i) k). Qed.
Lemma lem4454992 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (term474 K i k).
Proof. exact (TRANS (@lem4454986 K i k) (@lem4454990 K i k)). Qed.
Lemma lem4454993 {K : Type'} (i : K) (k : K -> Prop) : (term323 K i k) = (term475 K i k).
Proof. exact (MK_COMB (@lem4454975) (@lem4454992 K i k)). Qed.
Lemma lem4454994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4454995 {K : Type'} (i : K) (k : K -> Prop) : (term212 K i k) = (term476 K i k).
Proof. exact (MK_COMB (@lem4454994) (@lem4454993 K i k)). Qed.
Lemma lem4454996 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term168 A K k P f i) = (term536 A K k P f i).
Proof. exact (MK_COMB (@lem4454995 K i k) (@lem4454974 A K P f i)). Qed.
Lemma lem4454997 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term176 A K k P f) = (term537 A K k P f).
Proof. exact (fun_ext (fun i : K => @lem4454996 A K k P f i)). Qed.
Lemma lem4454998 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4454999 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term177 A K k P f) = (term538 A K k P f).
Proof. exact (MK_COMB (@lem4454998 K) (@lem4454997 A K k P f)). Qed.
Lemma lem4455000 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4455005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4455006 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4455005 K A f x). Qed.
Lemma lem4455008 {A K : Type'} (f : K -> A) (i : K) : (f i) = (@I (K -> A) f i).
Proof. exact (@lem4455006 A K f i). Qed.
Lemma lem4455013 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4455014 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4455013 K (A -> Prop) f x). Qed.
Lemma lem4455016 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4455014 A K s i). Qed.
Lemma lem4455017 {A K : Type'} (f : K -> A) (i : K) : (term464 A K f i) = (term465 A K f i).
Proof. exact (MK_COMB (@lem4455000 A) (@lem4455008 A K f i)). Qed.
Lemma lem4455018 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) : (term153 A K f s i) = (term466 A K f s i).
Proof. exact (MK_COMB (@lem4455017 A K f i) (@lem4455016 A K s i)). Qed.
Lemma lem4455020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4455021 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4455020 A (type686 A) f x). Qed.
Lemma lem4455022 {A K : Type'} (f : K -> A) (i : K) : (term465 A K f i) = (term467 A K f i).
Proof. exact (@lem4455021 A (@IN A) (@I (K -> A) f i)). Qed.
Lemma lem4455023 {A K : Type'} (s : type1470 A K) (i : K) : (@I (K -> A -> Prop) s i) = (@I (K -> A -> Prop) s i).
Proof. exact (eq_refl (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4455024 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) : (term466 A K f s i) = (term468 A K f s i).
Proof. exact (MK_COMB (@lem4455022 A K f i) (@lem4455023 A K s i)). Qed.
Lemma lem4455026 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4455027 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4455026 (A -> Prop) Prop f x). Qed.
Lemma lem4455028 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) : (term468 A K f s i) = (term469 A K f s i).
Proof. exact (@lem4455027 A (term467 A K f i) (@I (K -> A -> Prop) s i)). Qed.
Lemma lem4455029 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) : (term466 A K f s i) = (term469 A K f s i).
Proof. exact (TRANS (@lem4455024 A K f s i) (@lem4455028 A K f s i)). Qed.
Lemma lem4455030 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) : (term153 A K f s i) = (term469 A K f s i).
Proof. exact (TRANS (@lem4455018 A K f s i) (@lem4455029 A K f s i)). Qed.
Lemma lem4455031 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4455038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4455039 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem4455038 K (type686 K) f x). Qed.
Lemma lem4455040 {K : Type'} (i : K) : (@IN K i) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i).
Proof. exact (@lem4455039 K (@IN K) i). Qed.
Lemma lem4455041 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4455042 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) i k).
Proof. exact (MK_COMB (@lem4455040 K i) (@lem4455041 K k)). Qed.
Lemma lem4455044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4455045 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem4455044 (K -> Prop) Prop f x). Qed.
Lemma lem4455046 {K : Type'} (i : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) i k) = (term474 K i k).
Proof. exact (@lem4455045 K (@I (K -> (K -> Prop) -> Prop) (@IN K) i) k). Qed.
Lemma lem4455048 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (term474 K i k).
Proof. exact (TRANS (@lem4455042 K i k) (@lem4455046 K i k)). Qed.
Lemma lem4455049 {K : Type'} (i : K) (k : K -> Prop) : (term323 K i k) = (term475 K i k).
Proof. exact (MK_COMB (@lem4455031) (@lem4455048 K i k)). Qed.
Lemma lem4455050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4455051 {K : Type'} (i : K) (k : K -> Prop) : (term212 K i k) = (term476 K i k).
Proof. exact (MK_COMB (@lem4455050) (@lem4455049 K i k)). Qed.
Lemma lem4455052 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term154 A K k f s i) = (term539 A K k f s i).
Proof. exact (MK_COMB (@lem4455051 K i k) (@lem4455030 A K f s i)). Qed.
Lemma lem4455053 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term164 A K k f s) = (term540 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4455052 A K k f s i)). Qed.
Lemma lem4455054 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4455055 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term165 A K k f s) = (term541 A K k f s).
Proof. exact (MK_COMB (@lem4455054 K) (@lem4455053 A K k f s)). Qed.
Lemma lem4455056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4455057 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term183 A K k f s) = (term542 A K k f s).
Proof. exact (MK_COMB (@lem4455056) (@lem4455055 A K k f s)). Qed.
Lemma lem4455058 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term184 A K s k P f) = (term543 A K s k P f).
Proof. exact (MK_COMB (@lem4455057 A K k f s) (@lem4454999 A K k P f)). Qed.
Lemma lem4455059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4455060 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term248 A K s k P f) = (term544 A K s k P f).
Proof. exact (MK_COMB (@lem4455059) (@lem4455058 A K s k P f)). Qed.
Lemma lem4455061 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term264 A K f k s P i) = (term545 A K f k s P i).
Proof. exact (MK_COMB (@lem4455060 A K s k P f) (@lem4454950 A K k s P i)). Qed.
Lemma lem4455062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4455063 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term421 A K f k s P i) = (term546 A K f k s P i).
Proof. exact (MK_COMB (@lem4455062) (@lem4455061 A K f k s P i)). Qed.
Lemma lem4455064 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) : (term451 A K f i i' k s P x) = (term547 A K f i i' k s P x).
Proof. exact (MK_COMB (@lem4455063 A K f k s P i) (@lem4454879 A K i' k s P x)). Qed.
Lemma lem4455065 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term451 A K f i i' k s P x) : term547 A K f i i' k s P x.
Proof. exact (EQ_MP (@lem4455064 A K f i i' k s P x) (@lem4454646 A K f i i' k s P x h1)). Qed.
Lemma lem4455066 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term545 A K f k s P i.
Proof. exact (h1). Qed.
Lemma lem4455067 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term520 A K i' k s P x.
Proof. exact (h1). Qed.
Lemma lem4455068 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term535 A K k s P i.
Proof. exact (proj2 (@lem4455066 A K f k s P i h1)). Qed.
Lemma lem4455069 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term543 A K s k P f.
Proof. exact (proj1 (@lem4455066 A K f k s P i h1)). Qed.
Lemma lem4455070 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term533 A K s P i.
Proof. exact (proj2 (@lem4455068 A K f k s P i h1)). Qed.
Lemma lem4455072 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term538 A K k P f.
Proof. exact (proj2 (@lem4455069 A K f k s P i h1)). Qed.
Lemma lem4455073 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term541 A K k f s.
Proof. exact (proj1 (@lem4455069 A K f k s P i h1)). Qed.
Lemma lem4455074 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term479 A K k s P x.
Proof. exact (proj2 (@lem4455067 A K i' k s P x h1)). Qed.
Lemma lem4455075 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term518 A K s k P i'.
Proof. exact (proj1 (@lem4455067 A K i' k s P x h1)). Qed.
Lemma lem4455087 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term531 A K s P i x) = (term531 A K s P i x).
Proof. exact (eq_refl (term531 A K s P i x)). Qed.
Lemma lem4455088 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term532 A K s P i) = (term532 A K s P i).
Proof. exact (fun_ext (fun x : A => @lem4455087 A K s P i x)). Qed.
Lemma lem4455089 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4455091 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) : (term533 A K s P i) = (term533 A K s P i).
Proof. exact (MK_COMB (@lem4455089 A) (@lem4455088 A K s P i)). Qed.
Lemma lem4455092 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term533 A K s P i.
Proof. exact (EQ_MP (@lem4455091 A K s P i) (@lem4455070 A K f k s P i h1)). Qed.
Lemma lem4455100 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term539 A K k f s i) = (term539 A K k f s i).
Proof. exact (eq_refl (term539 A K k f s i)). Qed.
Lemma lem4455101 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term540 A K k f s) = (term540 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4455100 A K k f s i)). Qed.
Lemma lem4455102 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4455104 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term541 A K k f s) = (term541 A K k f s).
Proof. exact (MK_COMB (@lem4455102 K) (@lem4455101 A K k f s)). Qed.
Lemma lem4455105 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term541 A K k f s.
Proof. exact (EQ_MP (@lem4455104 A K k f s) (@lem4455073 A K f k s P i h1)). Qed.
Lemma lem4455113 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (i : K) : (term536 A K k P f i) = (term536 A K k P f i).
Proof. exact (eq_refl (term536 A K k P f i)). Qed.
Lemma lem4455114 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term537 A K k P f) = (term537 A K k P f).
Proof. exact (fun_ext (fun i : K => @lem4455113 A K k P f i)). Qed.
Lemma lem4455115 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4455117 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) : (term538 A K k P f) = (term538 A K k P f).
Proof. exact (MK_COMB (@lem4455115 K) (@lem4455114 A K k P f)). Qed.
Lemma lem4455118 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term538 A K k P f.
Proof. exact (EQ_MP (@lem4455117 A K k P f) (@lem4455072 A K f k s P i h1)). Qed.
Lemma lem4455133 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term516 A K s k P i' f) = (term548 A K k s P i' f).
Proof. exact (@lem19490 (term498 A K i' f k) (term513 A K k s i' f) (term491 A K P i' f)). Qed.
Lemma lem4455140 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term549 A K k s P i' f) = (term550 A K k s P i' f).
Proof. exact (@lem19699 (term498 A K i' f k) (term511 A K s i' f) (term491 A K P i' f)). Qed.
Lemma lem4455147 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term551 A K s i' f k) = (term552 A K s i' f k).
Proof. exact (@lem19699 (term498 A K i' f k) (term511 A K s i' f) (term498 A K i' f k)). Qed.
Lemma lem4455148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4455149 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (f : K -> A) (k : K -> Prop) : (term553 A K s i' f k) = (term554 A K s i' f k).
Proof. exact (MK_COMB (@lem4455148) (@lem4455147 A K s i' f k)). Qed.
Lemma lem4455150 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term548 A K k s P i' f) = (term555 A K k s P i' f).
Proof. exact (MK_COMB (@lem4455149 A K s i' f k) (@lem4455140 A K k s P i' f)). Qed.
Lemma lem4455152 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (f : K -> A) : (term516 A K s k P i' f) = (term555 A K k s P i' f).
Proof. exact (TRANS (@lem4455133 A K k s P i' f) (@lem4455150 A K k s P i' f)). Qed.
Lemma lem4455153 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) : (term517 A K s k P i') = (term556 A K k s P i').
Proof. exact (fun_ext (fun f : K -> A => @lem4455152 A K k s P i' f)). Qed.
Lemma lem4455154 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4455156 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) : (term518 A K s k P i') = (term557 A K k s P i').
Proof. exact (MK_COMB (@lem4455154 A K) (@lem4455153 A K k s P i')). Qed.
Lemma lem4455157 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term557 A K k s P i'.
Proof. exact (EQ_MP (@lem4455156 A K k s P i') (@lem4455075 A K i' k s P x h1)). Qed.
Lemma lem4455175 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (x : K -> A) (i : K) : (term477 A K k s P x i) = (term558 A K s k P x i).
Proof. exact (@lem19490 (term469 A K x s i) (term475 K i k) (term463 A K P x i)). Qed.
Lemma lem4455176 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (x : K -> A) : (term478 A K k s P x) = (term559 A K s k P x).
Proof. exact (fun_ext (fun i : K => @lem4455175 A K s k P x i)). Qed.
Lemma lem4455177 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4455179 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (x : K -> A) : (term479 A K k s P x) = (term560 A K s k P x).
Proof. exact (MK_COMB (@lem4455177 K) (@lem4455176 A K s k P x)). Qed.
Lemma lem4455180 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term560 A K s k P x.
Proof. exact (EQ_MP (@lem4455179 A K s k P x) (@lem4455074 A K i' k s P x h1)). Qed.
Lemma lem4455181 {A K : Type'} (_51521 : A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term561 A K s P i _51521.
Proof. exact (@lem4455092 A K f k s P i h1 _51521). Qed.
Lemma lem4455182 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (_51521 : A) : (term561 A K s P i _51521) = (term531 A K s P i _51521).
Proof. exact (eq_refl (term561 A K s P i _51521)). Qed.
Lemma lem4455184 {A K : Type'} (_51522 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term562 A K k f s _51522.
Proof. exact (@lem4455105 A K f k s P i h1 _51522). Qed.
Lemma lem4455185 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (_51522 : K) : (term562 A K k f s _51522) = (term539 A K k f s _51522).
Proof. exact (eq_refl (term562 A K k f s _51522)). Qed.
Lemma lem4455187 {A K : Type'} (_51523 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term563 A K k P f _51523.
Proof. exact (@lem4455118 A K f k s P i h1 _51523). Qed.
Lemma lem4455188 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (_51523 : K) : (term563 A K k P f _51523) = (term536 A K k P f _51523).
Proof. exact (eq_refl (term563 A K k P f _51523)). Qed.
Lemma lem4455190 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term564 A K k s P i' _51524.
Proof. exact (@lem4455157 A K i' k s P x h1 _51524). Qed.
Lemma lem4455191 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (_51524 : K -> A) : (term564 A K k s P i' _51524) = (term555 A K k s P i' _51524).
Proof. exact (eq_refl (term564 A K k s P i' _51524)). Qed.
Lemma lem4455192 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term555 A K k s P i' _51524.
Proof. exact (EQ_MP (@lem4455191 A K k s P i' _51524) (@lem4455190 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455193 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term565 A K s k P x _51525.
Proof. exact (@lem4455180 A K i' k s P x h1 _51525). Qed.
Lemma lem4455194 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (x : K -> A) (_51525 : K) : (term565 A K s k P x _51525) = (term558 A K s k P x _51525).
Proof. exact (eq_refl (term565 A K s k P x _51525)). Qed.
Lemma lem4455195 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term558 A K s k P x _51525.
Proof. exact (EQ_MP (@lem4455194 A K s k P x _51525) (@lem4455193 A K _51525 i' k s P x h1)). Qed.
Lemma lem4455198 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term550 A K k s P i' _51524.
Proof. exact (proj2 (@lem4455192 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455199 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term552 A K s i' _51524 k.
Proof. exact (proj1 (@lem4455192 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455211 {A K : Type'} (_51521 : A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term531 A K s P i _51521.
Proof. exact (EQ_MP (@lem4455182 A K s P i _51521) (@lem4455181 A K _51521 f k s P i h1)). Qed.
Lemma lem4455217 {A K : Type'} (_51522 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term539 A K k f s _51522.
Proof. exact (EQ_MP (@lem4455185 A K k f s _51522) (@lem4455184 A K _51522 f k s P i h1)). Qed.
Lemma lem4455223 {A K : Type'} (_51523 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term536 A K k P f _51523.
Proof. exact (EQ_MP (@lem4455188 A K k P f _51523) (@lem4455187 A K _51523 f k s P i h1)). Qed.
Lemma lem4455229 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term539 A K k x s _51525.
Proof. exact (proj1 (@lem4455195 A K _51525 i' k s P x h1)). Qed.
Lemma lem4455235 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term536 A K k P x _51525.
Proof. exact (proj2 (@lem4455195 A K _51525 i' k s P x h1)). Qed.
Lemma lem4455247 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term566 A K s P i' _51524.
Proof. exact (proj2 (@lem4455198 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455253 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term567 A K i' _51524 k.
Proof. exact (proj1 (@lem4455199 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455261 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term474 K i k.
Proof. exact (proj1 (@lem4455068 A K f k s P i h1)). Qed.
Lemma lem4455262 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term568 K i k.
Proof. exact (fun h0 : term475 K i k => @lem4455261 A K f k s P i h1). Qed.
Lemma lem4455264 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455265 {K : Type'} (i : K) (k : K -> Prop) : (term568 K i k) = (term474 K i k).
Proof. exact (@lem4455264 (term474 K i k)). Qed.
Lemma lem4455266 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term474 K i k.
Proof. exact (EQ_MP (@lem4455265 K i k) (@lem4455262 A K f k s P i h1)). Qed.
Lemma lem4455272 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4455273 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : (term539 A K k f s _51522) = (term570 A K f s _51522 k).
Proof. exact (@lem4455272 (term469 A K f s _51522) (term475 K _51522 k)). Qed.
Lemma lem4455279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4455280 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : (term571 A K k f s _51522) = (term572 A K f s _51522 k).
Proof. exact (MK_COMB (@lem4455279) (@lem4455273 A K f s _51522 k)). Qed.
Lemma lem4455286 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : (term570 A K f s _51522 k) = (term570 A K f s _51522 k).
Proof. exact (eq_refl (term570 A K f s _51522 k)). Qed.
Lemma lem4455287 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : ((term539 A K k f s _51522) = (term570 A K f s _51522 k)) = ((term570 A K f s _51522 k) = (term570 A K f s _51522 k)).
Proof. exact (MK_COMB (@lem4455280 A K f s _51522 k) (@lem4455286 A K f s _51522 k)). Qed.
Lemma lem4455289 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4455290 (x : Prop) : (x = x) = True.
Proof. exact (@lem4455289 Prop x). Qed.
Lemma lem4455291 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : ((term570 A K f s _51522 k) = (term570 A K f s _51522 k)) = True.
Proof. exact (@lem4455290 (term570 A K f s _51522 k)). Qed.
Lemma lem4455292 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : ((term539 A K k f s _51522) = (term570 A K f s _51522 k)) = True.
Proof. exact (TRANS (@lem4455287 A K f s _51522 k) (@lem4455291 A K f s _51522 k)). Qed.
Lemma lem4455293 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : True = ((term539 A K k f s _51522) = (term570 A K f s _51522 k)).
Proof. exact (SYM (@lem4455292 A K f s _51522 k)). Qed.
Lemma lem4455294 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) (k : K -> Prop) : (term539 A K k f s _51522) = (term570 A K f s _51522 k).
Proof. exact (EQ_MP (@lem4455293 A K f s _51522 k) (@lem0)). Qed.
Lemma lem4455295 {A K : Type'} (_51522 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term570 A K f s _51522 k.
Proof. exact (EQ_MP (@lem4455294 A K f s _51522 k) (@lem4455217 A K _51522 f k s P i h1)). Qed.
Lemma lem4455297 (b : Prop) (a : Prop) : (a \/ b) = (term573 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4455298 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (_51522 : K) : (term570 A K f s _51522 k) = (term574 A K k f s _51522).
Proof. exact (@lem4455297 (term475 K _51522 k) (term469 A K f s _51522)). Qed.
Lemma lem4455300 (a : Prop) : (term131 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4455301 {K : Type'} (_51522 : K) (k : K -> Prop) : (term575 K _51522 k) = (term474 K _51522 k).
Proof. exact (@lem4455300 (term474 K _51522 k)). Qed.
Lemma lem4455302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4455303 {K : Type'} (_51522 : K) (k : K -> Prop) : (term576 K _51522 k) = (term577 K _51522 k).
Proof. exact (MK_COMB (@lem4455302) (@lem4455301 K _51522 k)). Qed.
Lemma lem4455304 {A K : Type'} (f : K -> A) (s : type1470 A K) (_51522 : K) : (term469 A K f s _51522) = (term469 A K f s _51522).
Proof. exact (eq_refl (term469 A K f s _51522)). Qed.
Lemma lem4455305 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (_51522 : K) : (term574 A K k f s _51522) = (term578 A K k f s _51522).
Proof. exact (MK_COMB (@lem4455303 K _51522 k) (@lem4455304 A K f s _51522)). Qed.
Lemma lem4455306 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (_51522 : K) : (term570 A K f s _51522 k) = (term578 A K k f s _51522).
Proof. exact (TRANS (@lem4455298 A K k f s _51522) (@lem4455305 A K k f s _51522)). Qed.
Lemma lem4455309 {A K : Type'} (_51522 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term578 A K k f s _51522.
Proof. exact (EQ_MP (@lem4455306 A K k f s _51522) (@lem4455295 A K _51522 f k s P i h1)). Qed.
Lemma lem4455310 {A K : Type'} (_51522 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term578 A K k f s _51522.
Proof. exact (@lem4455309 A K _51522 f k s P i h1). Qed.
Lemma lem4455311 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term578 A K k f s i.
Proof. exact (@lem4455310 A K i f k s P i h1). Qed.
Lemma lem4455314 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term469 A K f s i.
Proof. exact (@lem4455311 A K f k s P i h1 (@lem4455266 A K f k s P i h1)). Qed.
Lemma lem4455315 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term579 A K f s i.
Proof. exact (fun h0 : term580 A K f s i => @lem4455314 A K f k s P i h1). Qed.
Lemma lem4455317 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455318 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) : (term579 A K f s i) = (term469 A K f s i).
Proof. exact (@lem4455317 (term469 A K f s i)). Qed.
Lemma lem4455319 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term469 A K f s i.
Proof. exact (EQ_MP (@lem4455318 A K f s i) (@lem4455315 A K f k s P i h1)). Qed.
Lemma lem4455321 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term474 K i k.
Proof. exact (proj1 (@lem4455068 A K f k s P i h1)). Qed.
Lemma lem4455322 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term568 K i k.
Proof. exact (fun h0 : term475 K i k => @lem4455321 A K f k s P i h1). Qed.
Lemma lem4455324 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455325 {K : Type'} (i : K) (k : K -> Prop) : (term568 K i k) = (term474 K i k).
Proof. exact (@lem4455324 (term474 K i k)). Qed.
Lemma lem4455326 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term474 K i k.
Proof. exact (EQ_MP (@lem4455325 K i k) (@lem4455322 A K f k s P i h1)). Qed.
Lemma lem4455332 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4455333 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : (term536 A K k P f _51523) = (term581 A K P f _51523 k).
Proof. exact (@lem4455332 (term463 A K P f _51523) (term475 K _51523 k)). Qed.
Lemma lem4455339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4455340 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : (term582 A K k P f _51523) = (term583 A K P f _51523 k).
Proof. exact (MK_COMB (@lem4455339) (@lem4455333 A K P f _51523 k)). Qed.
Lemma lem4455346 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : (term581 A K P f _51523 k) = (term581 A K P f _51523 k).
Proof. exact (eq_refl (term581 A K P f _51523 k)). Qed.
Lemma lem4455347 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : ((term536 A K k P f _51523) = (term581 A K P f _51523 k)) = ((term581 A K P f _51523 k) = (term581 A K P f _51523 k)).
Proof. exact (MK_COMB (@lem4455340 A K P f _51523 k) (@lem4455346 A K P f _51523 k)). Qed.
Lemma lem4455349 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4455350 (x : Prop) : (x = x) = True.
Proof. exact (@lem4455349 Prop x). Qed.
Lemma lem4455351 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : ((term581 A K P f _51523 k) = (term581 A K P f _51523 k)) = True.
Proof. exact (@lem4455350 (term581 A K P f _51523 k)). Qed.
Lemma lem4455352 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : ((term536 A K k P f _51523) = (term581 A K P f _51523 k)) = True.
Proof. exact (TRANS (@lem4455347 A K P f _51523 k) (@lem4455351 A K P f _51523 k)). Qed.
Lemma lem4455353 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : True = ((term536 A K k P f _51523) = (term581 A K P f _51523 k)).
Proof. exact (SYM (@lem4455352 A K P f _51523 k)). Qed.
Lemma lem4455354 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) (k : K -> Prop) : (term536 A K k P f _51523) = (term581 A K P f _51523 k).
Proof. exact (EQ_MP (@lem4455353 A K P f _51523 k) (@lem0)). Qed.
Lemma lem4455355 {A K : Type'} (_51523 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term581 A K P f _51523 k.
Proof. exact (EQ_MP (@lem4455354 A K P f _51523 k) (@lem4455223 A K _51523 f k s P i h1)). Qed.
Lemma lem4455357 (b : Prop) (a : Prop) : (a \/ b) = (term573 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4455358 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (_51523 : K) : (term581 A K P f _51523 k) = (term584 A K k P f _51523).
Proof. exact (@lem4455357 (term475 K _51523 k) (term463 A K P f _51523)). Qed.
Lemma lem4455360 (a : Prop) : (term131 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4455361 {K : Type'} (_51523 : K) (k : K -> Prop) : (term575 K _51523 k) = (term474 K _51523 k).
Proof. exact (@lem4455360 (term474 K _51523 k)). Qed.
Lemma lem4455362 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4455363 {K : Type'} (_51523 : K) (k : K -> Prop) : (term576 K _51523 k) = (term577 K _51523 k).
Proof. exact (MK_COMB (@lem4455362) (@lem4455361 K _51523 k)). Qed.
Lemma lem4455364 {A K : Type'} (P : type1470 A K) (f : K -> A) (_51523 : K) : (term463 A K P f _51523) = (term463 A K P f _51523).
Proof. exact (eq_refl (term463 A K P f _51523)). Qed.
Lemma lem4455365 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (_51523 : K) : (term584 A K k P f _51523) = (term585 A K k P f _51523).
Proof. exact (MK_COMB (@lem4455363 K _51523 k) (@lem4455364 A K P f _51523)). Qed.
Lemma lem4455366 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (f : K -> A) (_51523 : K) : (term581 A K P f _51523 k) = (term585 A K k P f _51523).
Proof. exact (TRANS (@lem4455358 A K k P f _51523) (@lem4455365 A K k P f _51523)). Qed.
Lemma lem4455369 {A K : Type'} (_51523 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term585 A K k P f _51523.
Proof. exact (EQ_MP (@lem4455366 A K k P f _51523) (@lem4455355 A K _51523 f k s P i h1)). Qed.
Lemma lem4455370 {A K : Type'} (_51523 : K) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term585 A K k P f _51523.
Proof. exact (@lem4455369 A K _51523 f k s P i h1). Qed.
Lemma lem4455371 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term585 A K k P f i.
Proof. exact (@lem4455370 A K i f k s P i h1). Qed.
Lemma lem4455374 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term463 A K P f i.
Proof. exact (@lem4455371 A K f k s P i h1 (@lem4455326 A K f k s P i h1)). Qed.
Lemma lem4455375 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term586 A K P f i.
Proof. exact (fun h0 : term587 A K P f i => @lem4455374 A K f k s P i h1). Qed.
Lemma lem4455377 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455378 {A K : Type'} (P : type1470 A K) (f : K -> A) (i : K) : (term586 A K P f i) = (term463 A K P f i).
Proof. exact (@lem4455377 (term463 A K P f i)). Qed.
Lemma lem4455379 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term463 A K P f i.
Proof. exact (EQ_MP (@lem4455378 A K P f i) (@lem4455375 A K f k s P i h1)). Qed.
Lemma lem4455381 (a : Prop) (b : Prop) : (term588 a b) = (term589 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4455382 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (_51521 : A) : (term531 A K s P i _51521) = (term590 A K s P i _51521).
Proof. exact (@lem4455381 (term526 A K _51521 s i) (term521 A K P i _51521)). Qed.
Lemma lem4455384 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4455385 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (_51521 : A) : (term590 A K s P i _51521) = (term591 A K s P i _51521).
Proof. exact (@lem4455384 (term592 A K s P i _51521)). Qed.
Lemma lem4455386 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (_51521 : A) : (term531 A K s P i _51521) = (term591 A K s P i _51521).
Proof. exact (TRANS (@lem4455382 A K s P i _51521) (@lem4455385 A K s P i _51521)). Qed.
Lemma lem4455388 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term473 A K s P f i.
Proof. exact (conj (@lem4455319 A K f k s P i h1) (@lem4455379 A K f k s P i h1)). Qed.
Lemma lem4455390 {A K : Type'} (_51521 : A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term591 A K s P i _51521.
Proof. exact (EQ_MP (@lem4455386 A K s P i _51521) (@lem4455211 A K _51521 f k s P i h1)). Qed.
Lemma lem4455391 {A K : Type'} (_51521 : A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term591 A K s P i _51521.
Proof. exact (@lem4455390 A K _51521 f k s P i h1). Qed.
Lemma lem4455392 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term593 A K s P f i.
Proof. exact (@lem4455391 A K (@I (K -> A) f i) f k s P i h1). Qed.
Lemma lem4455395 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : False.
Proof. exact (@lem4455392 A K f k s P i h1 (@lem4455388 A K f k s P i h1)). Qed.
Lemma lem4455396 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : term594.
Proof. exact (fun h0 : ~ False => @lem4455395 A K f k s P i h1). Qed.
Lemma lem4455398 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455399 : term594 = False.
Proof. exact (@lem4455398 False). Qed.
Lemma lem4455400 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (h1 : term545 A K f k s P i) : False.
Proof. exact (EQ_MP (@lem4455399) (@lem4455396 A K f k s P i h1)). Qed.
Lemma lem4455403 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) (h1 : term595 A K i' x k) : term595 A K i' x k.
Proof. exact (h1). Qed.
Lemma lem4455404 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) (h1 : term595 A K i' x k) : term596 A K i' x k.
Proof. exact (fun h0 : term498 A K i' x k => @lem4455403 A K i' x k h1). Qed.
Lemma lem4455406 (p : Prop) : (term597 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4455407 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) : (term596 A K i' x k) = (term595 A K i' x k).
Proof. exact (@lem4455406 (term498 A K i' x k)). Qed.
Lemma lem4455408 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) (h1 : term595 A K i' x k) : term595 A K i' x k.
Proof. exact (EQ_MP (@lem4455407 A K i' x k) (@lem4455404 A K i' x k h1)). Qed.
Lemma lem4455410 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4455411 (x : Prop) : (x = x) = True.
Proof. exact (@lem4455410 Prop x). Qed.
Lemma lem4455412 {A K : Type'} (i' : type803 A K) (_51524 : K -> A) (k : K -> Prop) : ((term567 A K i' _51524 k) = (term567 A K i' _51524 k)) = True.
Proof. exact (@lem4455411 (term567 A K i' _51524 k)). Qed.
Lemma lem4455413 {A K : Type'} (i' : type803 A K) (_51524 : K -> A) (k : K -> Prop) : True = ((term567 A K i' _51524 k) = (term567 A K i' _51524 k)).
Proof. exact (SYM (@lem4455412 A K i' _51524 k)). Qed.
Lemma lem4455414 {A K : Type'} (i' : type803 A K) (_51524 : K -> A) (k : K -> Prop) : (term567 A K i' _51524 k) = (term567 A K i' _51524 k).
Proof. exact (EQ_MP (@lem4455413 A K i' _51524 k) (@lem0)). Qed.
Lemma lem4455415 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term567 A K i' _51524 k.
Proof. exact (EQ_MP (@lem4455414 A K i' _51524 k) (@lem4455253 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455417 (b : Prop) (a : Prop) : (a \/ b) = (term573 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4455420 {A K : Type'} (i' : type803 A K) (_51524 : K -> A) (k : K -> Prop) : (term567 A K i' _51524 k) = (term598 A K i' _51524 k).
Proof. exact (@lem4455417 (term498 A K i' _51524 k) (term498 A K i' _51524 k)). Qed.
Lemma lem4455423 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' _51524 k.
Proof. exact (EQ_MP (@lem4455420 A K i' _51524 k) (@lem4455415 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455424 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' _51524 k.
Proof. exact (@lem4455423 A K _51524 i' k s P x h1). Qed.
Lemma lem4455425 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' x k.
Proof. exact (@lem4455424 A K x i' k s P x h1). Qed.
Lemma lem4455428 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term595 A K i' x k) (h2 : term520 A K i' k s P x) : term498 A K i' x k.
Proof. exact (@lem4455425 A K i' k s P x h2 (@lem4455408 A K i' x k h1)). Qed.
Lemma lem4455429 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' x k.
Proof. exact (fun h0 : term595 A K i' x k => @lem4455428 A K i' k s P x h0 h1). Qed.
Lemma lem4455431 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455432 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) : (term598 A K i' x k) = (term498 A K i' x k).
Proof. exact (@lem4455431 (term498 A K i' x k)). Qed.
Lemma lem4455433 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term498 A K i' x k.
Proof. exact (EQ_MP (@lem4455432 A K i' x k) (@lem4455429 A K i' k s P x h1)). Qed.
Lemma lem4455439 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4455440 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : (term539 A K k x s _51525) = (term570 A K x s _51525 k).
Proof. exact (@lem4455439 (term469 A K x s _51525) (term475 K _51525 k)). Qed.
Lemma lem4455446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4455447 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : (term571 A K k x s _51525) = (term572 A K x s _51525 k).
Proof. exact (MK_COMB (@lem4455446) (@lem4455440 A K x s _51525 k)). Qed.
Lemma lem4455453 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : (term570 A K x s _51525 k) = (term570 A K x s _51525 k).
Proof. exact (eq_refl (term570 A K x s _51525 k)). Qed.
Lemma lem4455454 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : ((term539 A K k x s _51525) = (term570 A K x s _51525 k)) = ((term570 A K x s _51525 k) = (term570 A K x s _51525 k)).
Proof. exact (MK_COMB (@lem4455447 A K x s _51525 k) (@lem4455453 A K x s _51525 k)). Qed.
Lemma lem4455456 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4455457 (x : Prop) : (x = x) = True.
Proof. exact (@lem4455456 Prop x). Qed.
Lemma lem4455458 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : ((term570 A K x s _51525 k) = (term570 A K x s _51525 k)) = True.
Proof. exact (@lem4455457 (term570 A K x s _51525 k)). Qed.
Lemma lem4455459 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : ((term539 A K k x s _51525) = (term570 A K x s _51525 k)) = True.
Proof. exact (TRANS (@lem4455454 A K x s _51525 k) (@lem4455458 A K x s _51525 k)). Qed.
Lemma lem4455460 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : True = ((term539 A K k x s _51525) = (term570 A K x s _51525 k)).
Proof. exact (SYM (@lem4455459 A K x s _51525 k)). Qed.
Lemma lem4455461 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) (k : K -> Prop) : (term539 A K k x s _51525) = (term570 A K x s _51525 k).
Proof. exact (EQ_MP (@lem4455460 A K x s _51525 k) (@lem0)). Qed.
Lemma lem4455462 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term570 A K x s _51525 k.
Proof. exact (EQ_MP (@lem4455461 A K x s _51525 k) (@lem4455229 A K _51525 i' k s P x h1)). Qed.
Lemma lem4455464 (b : Prop) (a : Prop) : (a \/ b) = (term573 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4455465 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_51525 : K) : (term570 A K x s _51525 k) = (term574 A K k x s _51525).
Proof. exact (@lem4455464 (term475 K _51525 k) (term469 A K x s _51525)). Qed.
Lemma lem4455467 (a : Prop) : (term131 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4455468 {K : Type'} (_51525 : K) (k : K -> Prop) : (term575 K _51525 k) = (term474 K _51525 k).
Proof. exact (@lem4455467 (term474 K _51525 k)). Qed.
Lemma lem4455469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4455470 {K : Type'} (_51525 : K) (k : K -> Prop) : (term576 K _51525 k) = (term577 K _51525 k).
Proof. exact (MK_COMB (@lem4455469) (@lem4455468 K _51525 k)). Qed.
Lemma lem4455471 {A K : Type'} (x : K -> A) (s : type1470 A K) (_51525 : K) : (term469 A K x s _51525) = (term469 A K x s _51525).
Proof. exact (eq_refl (term469 A K x s _51525)). Qed.
Lemma lem4455472 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_51525 : K) : (term574 A K k x s _51525) = (term578 A K k x s _51525).
Proof. exact (MK_COMB (@lem4455470 K _51525 k) (@lem4455471 A K x s _51525)). Qed.
Lemma lem4455473 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_51525 : K) : (term570 A K x s _51525 k) = (term578 A K k x s _51525).
Proof. exact (TRANS (@lem4455465 A K k x s _51525) (@lem4455472 A K k x s _51525)). Qed.
Lemma lem4455476 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term578 A K k x s _51525.
Proof. exact (EQ_MP (@lem4455473 A K k x s _51525) (@lem4455462 A K _51525 i' k s P x h1)). Qed.
Lemma lem4455477 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term578 A K k x s _51525.
Proof. exact (@lem4455476 A K _51525 i' k s P x h1). Qed.
Lemma lem4455478 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term599 A K k s i' x.
Proof. exact (@lem4455477 A K (@I ((K -> A) -> K) i' x) i' k s P x h1). Qed.
Lemma lem4455481 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term509 A K s i' x.
Proof. exact (@lem4455478 A K i' k s P x h1 (@lem4455433 A K i' k s P x h1)). Qed.
Lemma lem4455482 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term600 A K s i' x.
Proof. exact (fun h0 : term511 A K s i' x => @lem4455481 A K i' k s P x h1). Qed.
Lemma lem4455484 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455485 {A K : Type'} (s : type1470 A K) (i' : type803 A K) (x : K -> A) : (term600 A K s i' x) = (term509 A K s i' x).
Proof. exact (@lem4455484 (term509 A K s i' x)). Qed.
Lemma lem4455486 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term509 A K s i' x.
Proof. exact (EQ_MP (@lem4455485 A K s i' x) (@lem4455482 A K i' k s P x h1)). Qed.
Lemma lem4455489 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) (h1 : term595 A K i' x k) : term595 A K i' x k.
Proof. exact (h1). Qed.
Lemma lem4455490 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) (h1 : term595 A K i' x k) : term596 A K i' x k.
Proof. exact (fun h0 : term498 A K i' x k => @lem4455489 A K i' x k h1). Qed.
Lemma lem4455492 (p : Prop) : (term597 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4455493 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) : (term596 A K i' x k) = (term595 A K i' x k).
Proof. exact (@lem4455492 (term498 A K i' x k)). Qed.
Lemma lem4455494 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) (h1 : term595 A K i' x k) : term595 A K i' x k.
Proof. exact (EQ_MP (@lem4455493 A K i' x k) (@lem4455490 A K i' x k h1)). Qed.
Lemma lem4455496 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' _51524 k.
Proof. exact (EQ_MP (@lem4455420 A K i' _51524 k) (@lem4455415 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455497 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' _51524 k.
Proof. exact (@lem4455496 A K _51524 i' k s P x h1). Qed.
Lemma lem4455498 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' x k.
Proof. exact (@lem4455497 A K x i' k s P x h1). Qed.
Lemma lem4455501 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term595 A K i' x k) (h2 : term520 A K i' k s P x) : term498 A K i' x k.
Proof. exact (@lem4455498 A K i' k s P x h2 (@lem4455494 A K i' x k h1)). Qed.
Lemma lem4455502 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term598 A K i' x k.
Proof. exact (fun h0 : term595 A K i' x k => @lem4455501 A K i' k s P x h0 h1). Qed.
Lemma lem4455504 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455505 {A K : Type'} (i' : type803 A K) (x : K -> A) (k : K -> Prop) : (term598 A K i' x k) = (term498 A K i' x k).
Proof. exact (@lem4455504 (term498 A K i' x k)). Qed.
Lemma lem4455506 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term498 A K i' x k.
Proof. exact (EQ_MP (@lem4455505 A K i' x k) (@lem4455502 A K i' k s P x h1)). Qed.
Lemma lem4455512 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4455513 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : (term536 A K k P x _51525) = (term581 A K P x _51525 k).
Proof. exact (@lem4455512 (term463 A K P x _51525) (term475 K _51525 k)). Qed.
Lemma lem4455519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4455520 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : (term582 A K k P x _51525) = (term583 A K P x _51525 k).
Proof. exact (MK_COMB (@lem4455519) (@lem4455513 A K P x _51525 k)). Qed.
Lemma lem4455526 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : (term581 A K P x _51525 k) = (term581 A K P x _51525 k).
Proof. exact (eq_refl (term581 A K P x _51525 k)). Qed.
Lemma lem4455527 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : ((term536 A K k P x _51525) = (term581 A K P x _51525 k)) = ((term581 A K P x _51525 k) = (term581 A K P x _51525 k)).
Proof. exact (MK_COMB (@lem4455520 A K P x _51525 k) (@lem4455526 A K P x _51525 k)). Qed.
Lemma lem4455529 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4455530 (x : Prop) : (x = x) = True.
Proof. exact (@lem4455529 Prop x). Qed.
Lemma lem4455531 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : ((term581 A K P x _51525 k) = (term581 A K P x _51525 k)) = True.
Proof. exact (@lem4455530 (term581 A K P x _51525 k)). Qed.
Lemma lem4455532 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : ((term536 A K k P x _51525) = (term581 A K P x _51525 k)) = True.
Proof. exact (TRANS (@lem4455527 A K P x _51525 k) (@lem4455531 A K P x _51525 k)). Qed.
Lemma lem4455533 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : True = ((term536 A K k P x _51525) = (term581 A K P x _51525 k)).
Proof. exact (SYM (@lem4455532 A K P x _51525 k)). Qed.
Lemma lem4455534 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) (k : K -> Prop) : (term536 A K k P x _51525) = (term581 A K P x _51525 k).
Proof. exact (EQ_MP (@lem4455533 A K P x _51525 k) (@lem0)). Qed.
Lemma lem4455535 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term581 A K P x _51525 k.
Proof. exact (EQ_MP (@lem4455534 A K P x _51525 k) (@lem4455235 A K _51525 i' k s P x h1)). Qed.
Lemma lem4455537 (b : Prop) (a : Prop) : (a \/ b) = (term573 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4455538 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (x : K -> A) (_51525 : K) : (term581 A K P x _51525 k) = (term584 A K k P x _51525).
Proof. exact (@lem4455537 (term475 K _51525 k) (term463 A K P x _51525)). Qed.
Lemma lem4455540 (a : Prop) : (term131 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4455541 {K : Type'} (_51525 : K) (k : K -> Prop) : (term575 K _51525 k) = (term474 K _51525 k).
Proof. exact (@lem4455540 (term474 K _51525 k)). Qed.
Lemma lem4455542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4455543 {K : Type'} (_51525 : K) (k : K -> Prop) : (term576 K _51525 k) = (term577 K _51525 k).
Proof. exact (MK_COMB (@lem4455542) (@lem4455541 K _51525 k)). Qed.
Lemma lem4455544 {A K : Type'} (P : type1470 A K) (x : K -> A) (_51525 : K) : (term463 A K P x _51525) = (term463 A K P x _51525).
Proof. exact (eq_refl (term463 A K P x _51525)). Qed.
Lemma lem4455545 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (x : K -> A) (_51525 : K) : (term584 A K k P x _51525) = (term585 A K k P x _51525).
Proof. exact (MK_COMB (@lem4455543 K _51525 k) (@lem4455544 A K P x _51525)). Qed.
Lemma lem4455546 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (x : K -> A) (_51525 : K) : (term581 A K P x _51525 k) = (term585 A K k P x _51525).
Proof. exact (TRANS (@lem4455538 A K k P x _51525) (@lem4455545 A K k P x _51525)). Qed.
Lemma lem4455549 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term585 A K k P x _51525.
Proof. exact (EQ_MP (@lem4455546 A K k P x _51525) (@lem4455535 A K _51525 i' k s P x h1)). Qed.
Lemma lem4455550 {A K : Type'} (_51525 : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term585 A K k P x _51525.
Proof. exact (@lem4455549 A K _51525 i' k s P x h1). Qed.
Lemma lem4455551 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term601 A K k P i' x.
Proof. exact (@lem4455550 A K (@I ((K -> A) -> K) i' x) i' k s P x h1). Qed.
Lemma lem4455554 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term489 A K P i' x.
Proof. exact (@lem4455551 A K i' k s P x h1 (@lem4455506 A K i' k s P x h1)). Qed.
Lemma lem4455555 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term602 A K P i' x.
Proof. exact (fun h0 : term491 A K P i' x => @lem4455554 A K i' k s P x h1). Qed.
Lemma lem4455557 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455558 {A K : Type'} (P : type1470 A K) (i' : type803 A K) (x : K -> A) : (term602 A K P i' x) = (term489 A K P i' x).
Proof. exact (@lem4455557 (term489 A K P i' x)). Qed.
Lemma lem4455559 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term489 A K P i' x.
Proof. exact (EQ_MP (@lem4455558 A K P i' x) (@lem4455555 A K i' k s P x h1)). Qed.
Lemma lem4455561 (a : Prop) (b : Prop) : (term588 a b) = (term589 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4455562 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (_51524 : K -> A) : (term566 A K s P i' _51524) = (term603 A K s P i' _51524).
Proof. exact (@lem4455561 (term509 A K s i' _51524) (term489 A K P i' _51524)). Qed.
Lemma lem4455564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4455565 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (_51524 : K -> A) : (term603 A K s P i' _51524) = (term604 A K s P i' _51524).
Proof. exact (@lem4455564 (term605 A K s P i' _51524)). Qed.
Lemma lem4455566 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i' : type803 A K) (_51524 : K -> A) : (term566 A K s P i' _51524) = (term604 A K s P i' _51524).
Proof. exact (TRANS (@lem4455562 A K s P i' _51524) (@lem4455565 A K s P i' _51524)). Qed.
Lemma lem4455568 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term605 A K s P i' x.
Proof. exact (conj (@lem4455486 A K i' k s P x h1) (@lem4455559 A K i' k s P x h1)). Qed.
Lemma lem4455570 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term604 A K s P i' _51524.
Proof. exact (EQ_MP (@lem4455566 A K s P i' _51524) (@lem4455247 A K _51524 i' k s P x h1)). Qed.
Lemma lem4455571 {A K : Type'} (_51524 : K -> A) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term604 A K s P i' _51524.
Proof. exact (@lem4455570 A K _51524 i' k s P x h1). Qed.
Lemma lem4455572 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term604 A K s P i' x.
Proof. exact (@lem4455571 A K x i' k s P x h1). Qed.
Lemma lem4455575 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : False.
Proof. exact (@lem4455572 A K i' k s P x h1 (@lem4455568 A K i' k s P x h1)). Qed.
Lemma lem4455576 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : term594.
Proof. exact (fun h0 : ~ False => @lem4455575 A K i' k s P x h1). Qed.
Lemma lem4455578 (p : Prop) : (term569 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4455579 : term594 = False.
Proof. exact (@lem4455578 False). Qed.
Lemma lem4455580 {A K : Type'} (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term520 A K i' k s P x) : False.
Proof. exact (EQ_MP (@lem4455579) (@lem4455576 A K i' k s P x h1)). Qed.
Lemma lem4455581 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (x : K -> A) (h1 : term451 A K f i i' k s P x) : False.
Proof. exact (or_elim (@lem4455065 A K f i i' k s P x h1) (fun h0 : term545 A K f k s P i => @lem4455400 A K f k s P i h0) (fun h0 : term520 A K i' k s P x => @lem4455580 A K i' k s P x h0)). Qed.
Lemma lem4455582 {A K : Type'} (f : K -> A) (i : K) (i' : type803 A K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term454 A K f i i' k s P) : False.
Proof. exact (ex_elim (@lem4454645 A K f i i' k s P h1) (fun x : K -> A => fun h0 : term453 A K f i i' k s P x => @lem4455581 A K f i i' k s P x h0)). Qed.
Lemma lem4455583 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term456 A K f i k s P) : False.
Proof. exact (ex_elim (@lem4454644 A K f i k s P h1) (fun i' : type803 A K => fun h0 : term455 A K f i k s P i' => @lem4455582 A K f i i' k s P h0)). Qed.
Lemma lem4455584 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term458 A K f k s P) : False.
Proof. exact (ex_elim (@lem4454643 A K f k s P h1) (fun i : K => fun h0 : term457 A K f k s P i => @lem4455583 A K f i k s P h0)). Qed.
Lemma lem4455585 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : False.
Proof. exact (ex_elim (@lem4454642 A K k s P h1) (fun f : K -> A => fun h0 : term459 A K k s P f => @lem4455584 A K f k s P h0)). Qed.
Lemma lem4455586 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : (term126 A K k s P) = False.
Proof. exact (prop_ext (fun h2 : term126 A K k s P => @lem4455585 A K k s P h1) (fun h2 : False => @lem4453699 A K k s P h1)). Qed.
Lemma lem4455587 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : False.
Proof. exact (EQ_MP (@lem4455586 A K k s P h1) (@lem4453699 A K k s P h1)). Qed.
Lemma lem4455588 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term125 A K k s P.
Proof. exact (fun h0 : term126 A K k s P => @lem4455587 A K k s P h0). Qed.
Lemma lem4455589 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term122 A K s k P) = (term84 A K k s P).
Proof. exact (EQ_MP (@lem4453698 A K k s P) (@lem4455588 A K k s P)). Qed.
Lemma lem4455594 {A K : Type'} (s : type1470 A K) (P : type1470 A K) : term135 A K s P.
Proof. exact (fun k : K -> Prop => @lem4455589 A K k s P). Qed.
Lemma lem4455599 {A K : Type'} (P : type1470 A K) : term139 A K P.
Proof. exact (fun s : type1470 A K => @lem4455594 A K s P). Qed.
Lemma lem4455604 {A K : Type'} : term143 A K.
Proof. exact (fun P : type1470 A K => @lem4455599 A K P). Qed.
Lemma lem4455605 {A K : Type'} : term142 A K.
Proof. exact (EQ_MP (@lem4453694 A K) (@lem4455604 A K)). Qed.
Lemma lem4455606 {A K : Type'} (P : type1470 A K) : term606 A K P.
Proof. exact (@lem4455605 A K P). Qed.
Lemma lem4455607 {A K : Type'} (P : type1470 A K) : (term606 A K P) = (term138 A K P).
Proof. exact (eq_refl (term606 A K P)). Qed.
Lemma lem4455608 {A K : Type'} (P : type1470 A K) : term138 A K P.
Proof. exact (EQ_MP (@lem4455607 A K P) (@lem4455606 A K P)). Qed.
Lemma lem4455609 {A K : Type'} (P : type1470 A K) (s : type1470 A K) : term607 A K P s.
Proof. exact (@lem4455608 A K P s). Qed.
Lemma lem4455610 {A K : Type'} (s : type1470 A K) (P : type1470 A K) : (term607 A K P s) = (term134 A K s P).
Proof. exact (eq_refl (term607 A K P s)). Qed.
Lemma lem4455611 {A K : Type'} (s : type1470 A K) (P : type1470 A K) : term134 A K s P.
Proof. exact (EQ_MP (@lem4455610 A K s P) (@lem4455609 A K P s)). Qed.
Lemma lem4455612 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (k : K -> Prop) : term608 A K s P k.
Proof. exact (@lem4455611 A K s P k). Qed.
Lemma lem4455613 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term608 A K s P k) = (term125 A K k s P).
Proof. exact (eq_refl (term608 A K s P k)). Qed.
Lemma lem4455614 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term125 A K k s P.
Proof. exact (EQ_MP (@lem4455613 A K k s P) (@lem4455612 A K s P k)). Qed.
Lemma lem4455616 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term125 A K k s P.
Proof. exact (@lem4453421 A K k s P (@lem4455614 A K k s P)). Qed.
Lemma lem4455617 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : False.
Proof. exact (@lem4455616 A K k s P (@lem4453405 A K k s P h1)). Qed.
Lemma lem4455618 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : (term126 A K k s P) = False.
Proof. exact (prop_ext (fun h2 : term126 A K k s P => @lem4455617 A K k s P h1) (fun h2 : False => @lem4453405 A K k s P h1)). Qed.
Lemma lem4455619 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term126 A K k s P) : False.
Proof. exact (EQ_MP (@lem4455618 A K k s P h1) (@lem4453405 A K k s P h1)). Qed.
Lemma lem4455620 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : term125 A K k s P.
Proof. exact (fun h0 : term126 A K k s P => @lem4455619 A K k s P h0). Qed.
Lemma lem4455621 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term122 A K s k P) = (term84 A K k s P).
Proof. exact (EQ_MP (@lem4453404 A K k s P) (@lem4455620 A K k s P)). Qed.
Lemma lem4455622 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term81 A K s P k) = (term84 A K k s P).
Proof. exact (EQ_MP (@lem4453400 A K k s P) (@lem4455621 A K k s P)). Qed.
Lemma lem4455623 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term25 A K s k P) = (term84 A K k s P).
Proof. exact (EQ_MP (@lem4452833 A K k s P) (@lem4455622 A K k s P)). Qed.
Lemma lem4455628 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : term609 A K k P.
Proof. exact (fun s : type1470 A K => @lem4455623 A K k s P). Qed.
Lemma lem4455633 {A K : Type'} (P : type1470 A K) : term610 A K P.
Proof. exact (fun k : K -> Prop => @lem4455628 A K k P). Qed.
Lemma lem4455638 {A K : Type'} : term611 A K.
Proof. exact (fun P : type1470 A K => @lem4455633 A K P). Qed.
