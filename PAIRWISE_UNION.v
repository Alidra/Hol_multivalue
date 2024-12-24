Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Lemma lem4813740 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4813741 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4813742 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4813741 t1) (@lem4813740 t1)). Qed.
Lemma lem4813743 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4813742 t1 t2). Qed.
Lemma lem4813744 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4813745 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4813744 t1 t2) (@lem4813743 t1 t2)). Qed.
Lemma lem4813746 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4813745 t1 t2 t3). Qed.
Lemma lem4813747 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4813748 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4813747 t1 t2 t3) (@lem4813746 t1 t2 t3)). Qed.
Lemma lem4813749 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4813748 t1 t2 t3)). Qed.
Lemma lem4813750 {_110510 : Type'} (s : _110510 -> Prop) : term7 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4813751 {_110510 : Type'} (s : _110510 -> Prop) : (term7 _110510 s) = (term8 _110510 s).
Proof. exact (eq_refl (term7 _110510 s)). Qed.
Lemma lem4813752 {_110510 : Type'} (s : _110510 -> Prop) : term8 _110510 s.
Proof. exact (EQ_MP (@lem4813751 _110510 s) (@lem4813750 _110510 s)). Qed.
Lemma lem4813753 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term9 _110510 s r.
Proof. exact (@lem4813752 _110510 s r). Qed.
Lemma lem4813754 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term9 _110510 s r) = ((@pairwise _110510 r s) = (term10 _110510 s r)).
Proof. exact (eq_refl (term9 _110510 s r)). Qed.
Lemma lem4813771 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4813754 _110510 s r) (@lem4813753 _110510 s r)). Qed.
Lemma lem4813772 {_110859 : Type'} (s : _110859 -> Prop) (r : type1402 _110859) : (@pairwise _110859 r s) = (term10 _110859 s r).
Proof. exact (@lem4813771 _110859 s r). Qed.
Lemma lem4813773 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term11 _110859 R s t) = (term12 _110859 s t R).
Proof. exact (@lem4813772 _110859 (@UNION _110859 s t) R). Qed.
Lemma lem4813790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4813791 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term13 _110859 R s t) = (term14 _110859 s t R).
Proof. exact (MK_COMB (@lem4813790) (@lem4813773 _110859 s t R)). Qed.
Lemma lem4813795 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4813754 _110510 s r) (@lem4813753 _110510 s r)). Qed.
Lemma lem4813796 {_110859 : Type'} (s : _110859 -> Prop) (r : type1402 _110859) : (@pairwise _110859 r s) = (term10 _110859 s r).
Proof. exact (@lem4813795 _110859 s r). Qed.
Lemma lem4813797 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (@pairwise _110859 R s) = (term10 _110859 s R).
Proof. exact (@lem4813796 _110859 s R). Qed.
Lemma lem4813814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4813815 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term15 _110859 R s) = (term16 _110859 s R).
Proof. exact (MK_COMB (@lem4813814) (@lem4813797 _110859 s R)). Qed.
Lemma lem4813819 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4813754 _110510 s r) (@lem4813753 _110510 s r)). Qed.
Lemma lem4813820 {_110859 : Type'} (s : _110859 -> Prop) (r : type1402 _110859) : (@pairwise _110859 r s) = (term10 _110859 s r).
Proof. exact (@lem4813819 _110859 s r). Qed.
Lemma lem4813821 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (@pairwise _110859 R t) = (term10 _110859 t R).
Proof. exact (@lem4813820 _110859 t R). Qed.
Lemma lem4813838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4813839 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term15 _110859 R t) = (term16 _110859 t R).
Proof. exact (MK_COMB (@lem4813838) (@lem4813821 _110859 t R)). Qed.
Lemma lem4813854 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term17 _110859 t s R) = (term17 _110859 t s R).
Proof. exact (eq_refl (term17 _110859 t s R)). Qed.
Lemma lem4813855 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term18 _110859 t s R) = (term19 _110859 t s R).
Proof. exact (MK_COMB (@lem4813839 _110859 t R) (@lem4813854 _110859 t s R)). Qed.
Lemma lem4813858 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term20 _110859 t s R) = (term21 _110859 t s R).
Proof. exact (MK_COMB (@lem4813815 _110859 s R) (@lem4813855 _110859 t s R)). Qed.
Lemma lem4813861 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term11 _110859 R s t) = (term20 _110859 t s R)) = ((term12 _110859 s t R) = (term21 _110859 t s R)).
Proof. exact (MK_COMB (@lem4813791 _110859 s t R) (@lem4813858 _110859 t s R)). Qed.
Lemma lem4813864 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term22 _110859 s R) = (term23 _110859 s R).
Proof. exact (fun_ext (fun t : _110859 -> Prop => @lem4813861 _110859 t s R)). Qed.
Lemma lem4813865 {_110859 : Type'} : (@all (_110859 -> Prop)) = (@all (_110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> Prop))). Qed.
Lemma lem4813866 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term24 _110859 s R) = (term25 _110859 s R).
Proof. exact (MK_COMB (@lem4813865 _110859) (@lem4813864 _110859 s R)). Qed.
Lemma lem4813871 {_110859 : Type'} (R : type1402 _110859) : (term26 _110859 R) = (term27 _110859 R).
Proof. exact (fun_ext (fun s : _110859 -> Prop => @lem4813866 _110859 s R)). Qed.
Lemma lem4813872 {_110859 : Type'} : (@all (_110859 -> Prop)) = (@all (_110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> Prop))). Qed.
Lemma lem4813873 {_110859 : Type'} (R : type1402 _110859) : (term28 _110859 R) = (term29 _110859 R).
Proof. exact (MK_COMB (@lem4813872 _110859) (@lem4813871 _110859 R)). Qed.
Lemma lem4813878 {_110859 : Type'} : (term30 _110859) = (term31 _110859).
Proof. exact (fun_ext (fun R : type1402 _110859 => @lem4813873 _110859 R)). Qed.
Lemma lem4813879 {_110859 : Type'} : (@all (_110859 -> _110859 -> Prop)) = (@all (_110859 -> _110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> _110859 -> Prop))). Qed.
Lemma lem4813880 {_110859 : Type'} : (term32 _110859) = (term33 _110859).
Proof. exact (MK_COMB (@lem4813879 _110859) (@lem4813878 _110859)). Qed.
Lemma lem4813885 {_110859 : Type'} : (term33 _110859) = (term32 _110859).
Proof. exact (SYM (@lem4813880 _110859)). Qed.
Lemma lem4814003 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term34 A x s t) = (term35 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4814004 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (t : _110859 -> Prop) : (term34 _110859 x s t) = (term35 _110859 s x t).
Proof. exact (@lem4814003 _110859 s x t). Qed.
Lemma lem4814008 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814009 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814008 _110859 P x). Qed.
Lemma lem4814010 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (@IN _110859 x s) = (s x).
Proof. exact (@lem4814009 _110859 s x). Qed.
Lemma lem4814011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814012 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term36 _110859 x s) = (term37 _110859 s x).
Proof. exact (MK_COMB (@lem4814011) (@lem4814010 _110859 s x)). Qed.
Lemma lem4814014 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814015 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814014 _110859 P x). Qed.
Lemma lem4814016 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (@IN _110859 x t) = (t x).
Proof. exact (@lem4814015 _110859 t x). Qed.
Lemma lem4814017 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term35 _110859 s x t) = (term38 _110859 s t x).
Proof. exact (MK_COMB (@lem4814012 _110859 s x) (@lem4814016 _110859 t x)). Qed.
Lemma lem4814020 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term34 _110859 x s t) = (term38 _110859 s t x).
Proof. exact (TRANS (@lem4814004 _110859 s x t) (@lem4814017 _110859 s t x)). Qed.
Lemma lem4814021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814022 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term39 _110859 x s t) = (term40 _110859 s t x).
Proof. exact (MK_COMB (@lem4814021) (@lem4814020 _110859 s t x)). Qed.
Lemma lem4814026 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term34 A x s t) = (term35 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4814027 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (t : _110859 -> Prop) : (term34 _110859 x s t) = (term35 _110859 s x t).
Proof. exact (@lem4814026 _110859 s x t). Qed.
Lemma lem4814028 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (t : _110859 -> Prop) : (term34 _110859 y s t) = (term35 _110859 s y t).
Proof. exact (@lem4814027 _110859 s y t). Qed.
Lemma lem4814032 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814033 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814032 _110859 P x). Qed.
Lemma lem4814034 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (@IN _110859 y s) = (s y).
Proof. exact (@lem4814033 _110859 s y). Qed.
Lemma lem4814035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814036 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term36 _110859 y s) = (term37 _110859 s y).
Proof. exact (MK_COMB (@lem4814035) (@lem4814034 _110859 s y)). Qed.
Lemma lem4814038 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814039 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814038 _110859 P x). Qed.
Lemma lem4814040 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (@IN _110859 y t) = (t y).
Proof. exact (@lem4814039 _110859 t y). Qed.
Lemma lem4814041 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (y : _110859) : (term35 _110859 s y t) = (term38 _110859 s t y).
Proof. exact (MK_COMB (@lem4814036 _110859 s y) (@lem4814040 _110859 t y)). Qed.
Lemma lem4814044 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (y : _110859) : (term34 _110859 y s t) = (term38 _110859 s t y).
Proof. exact (TRANS (@lem4814028 _110859 s y t) (@lem4814041 _110859 s t y)). Qed.
Lemma lem4814045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814046 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (y : _110859) : (term39 _110859 y s t) = (term40 _110859 s t y).
Proof. exact (MK_COMB (@lem4814045) (@lem4814044 _110859 s t y)). Qed.
Lemma lem4814049 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term41 _110859 x y).
Proof. exact (eq_refl (term41 _110859 x y)). Qed.
Lemma lem4814050 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term42 _110859 s t x y) = (term43 _110859 s t x y).
Proof. exact (MK_COMB (@lem4814046 _110859 s t y) (@lem4814049 _110859 x y)). Qed.
Lemma lem4814053 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term44 _110859 s t x y) = (term45 _110859 s t x y).
Proof. exact (MK_COMB (@lem4814022 _110859 s t x) (@lem4814050 _110859 s t x y)). Qed.
Lemma lem4814056 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4814057 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term46 _110859 s t x y) = (term47 _110859 s t x y).
Proof. exact (MK_COMB (@lem4814056) (@lem4814053 _110859 s t x y)). Qed.
Lemma lem4814058 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4814059 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term48 _110859 s t R x y) = (term49 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4814057 _110859 s t x y) (@lem4814058 _110859 R x y)). Qed.
Lemma lem4814062 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term50 _110859 s t R x) = (term51 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814059 _110859 s t R x y)). Qed.
Lemma lem4814063 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814064 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term52 _110859 s t R x) = (term53 _110859 s t R x).
Proof. exact (MK_COMB (@lem4814063 _110859) (@lem4814062 _110859 s t R x)). Qed.
Lemma lem4814069 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term54 _110859 s t R) = (term55 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814064 _110859 s t R x)). Qed.
Lemma lem4814070 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814071 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term12 _110859 s t R) = (term56 _110859 s t R).
Proof. exact (MK_COMB (@lem4814070 _110859) (@lem4814069 _110859 s t R)). Qed.
Lemma lem4814076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4814077 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term14 _110859 s t R) = (term57 _110859 s t R).
Proof. exact (MK_COMB (@lem4814076) (@lem4814071 _110859 s t R)). Qed.
Lemma lem4814093 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814094 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814093 _110859 P x). Qed.
Lemma lem4814095 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (@IN _110859 x s) = (s x).
Proof. exact (@lem4814094 _110859 s x). Qed.
Lemma lem4814096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814097 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term58 _110859 x s) = (term59 _110859 s x).
Proof. exact (MK_COMB (@lem4814096) (@lem4814095 _110859 s x)). Qed.
Lemma lem4814101 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814102 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814101 _110859 P x). Qed.
Lemma lem4814103 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (@IN _110859 y s) = (s y).
Proof. exact (@lem4814102 _110859 s y). Qed.
Lemma lem4814104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814105 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term58 _110859 y s) = (term59 _110859 s y).
Proof. exact (MK_COMB (@lem4814104) (@lem4814103 _110859 s y)). Qed.
Lemma lem4814108 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term41 _110859 x y).
Proof. exact (eq_refl (term41 _110859 x y)). Qed.
Lemma lem4814109 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term60 _110859 s x y) = (term61 _110859 s x y).
Proof. exact (MK_COMB (@lem4814105 _110859 s y) (@lem4814108 _110859 x y)). Qed.
Lemma lem4814112 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term62 _110859 s x y) = (term63 _110859 s x y).
Proof. exact (MK_COMB (@lem4814097 _110859 s x) (@lem4814109 _110859 s x y)). Qed.
Lemma lem4814115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4814116 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term64 _110859 s x y) = (term65 _110859 s x y).
Proof. exact (MK_COMB (@lem4814115) (@lem4814112 _110859 s x y)). Qed.
Lemma lem4814117 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4814118 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term66 _110859 s R x y) = (term67 _110859 s R x y).
Proof. exact (MK_COMB (@lem4814116 _110859 s x y) (@lem4814117 _110859 R x y)). Qed.
Lemma lem4814121 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term68 _110859 s R x) = (term69 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814118 _110859 s R x y)). Qed.
Lemma lem4814122 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814123 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term70 _110859 s R x) = (term71 _110859 s R x).
Proof. exact (MK_COMB (@lem4814122 _110859) (@lem4814121 _110859 s R x)). Qed.
Lemma lem4814128 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term72 _110859 s R) = (term73 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814123 _110859 s R x)). Qed.
Lemma lem4814129 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814130 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term10 _110859 s R) = (term74 _110859 s R).
Proof. exact (MK_COMB (@lem4814129 _110859) (@lem4814128 _110859 s R)). Qed.
Lemma lem4814135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814136 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term16 _110859 s R) = (term75 _110859 s R).
Proof. exact (MK_COMB (@lem4814135) (@lem4814130 _110859 s R)). Qed.
Lemma lem4814152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814153 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814152 _110859 P x). Qed.
Lemma lem4814154 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (@IN _110859 x t) = (t x).
Proof. exact (@lem4814153 _110859 t x). Qed.
Lemma lem4814155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814156 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term58 _110859 x t) = (term59 _110859 t x).
Proof. exact (MK_COMB (@lem4814155) (@lem4814154 _110859 t x)). Qed.
Lemma lem4814160 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814161 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814160 _110859 P x). Qed.
Lemma lem4814162 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (@IN _110859 y t) = (t y).
Proof. exact (@lem4814161 _110859 t y). Qed.
Lemma lem4814163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814164 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term58 _110859 y t) = (term59 _110859 t y).
Proof. exact (MK_COMB (@lem4814163) (@lem4814162 _110859 t y)). Qed.
Lemma lem4814167 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term41 _110859 x y).
Proof. exact (eq_refl (term41 _110859 x y)). Qed.
Lemma lem4814168 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term60 _110859 t x y) = (term61 _110859 t x y).
Proof. exact (MK_COMB (@lem4814164 _110859 t y) (@lem4814167 _110859 x y)). Qed.
Lemma lem4814171 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term62 _110859 t x y) = (term63 _110859 t x y).
Proof. exact (MK_COMB (@lem4814156 _110859 t x) (@lem4814168 _110859 t x y)). Qed.
Lemma lem4814174 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4814175 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term64 _110859 t x y) = (term65 _110859 t x y).
Proof. exact (MK_COMB (@lem4814174) (@lem4814171 _110859 t x y)). Qed.
Lemma lem4814176 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4814177 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term66 _110859 t R x y) = (term67 _110859 t R x y).
Proof. exact (MK_COMB (@lem4814175 _110859 t x y) (@lem4814176 _110859 R x y)). Qed.
Lemma lem4814180 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term68 _110859 t R x) = (term69 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814177 _110859 t R x y)). Qed.
Lemma lem4814181 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814182 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term70 _110859 t R x) = (term71 _110859 t R x).
Proof. exact (MK_COMB (@lem4814181 _110859) (@lem4814180 _110859 t R x)). Qed.
Lemma lem4814187 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term72 _110859 t R) = (term73 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814182 _110859 t R x)). Qed.
Lemma lem4814188 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814189 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term10 _110859 t R) = (term74 _110859 t R).
Proof. exact (MK_COMB (@lem4814188 _110859) (@lem4814187 _110859 t R)). Qed.
Lemma lem4814194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814195 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term16 _110859 t R) = (term75 _110859 t R).
Proof. exact (MK_COMB (@lem4814194) (@lem4814189 _110859 t R)). Qed.
Lemma lem4814209 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term76 A x s t) = (term77 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4814210 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (t : _110859 -> Prop) : (term76 _110859 x s t) = (term77 _110859 s x t).
Proof. exact (@lem4814209 _110859 s x t). Qed.
Lemma lem4814214 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814215 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814214 _110859 P x). Qed.
Lemma lem4814216 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (@IN _110859 x s) = (s x).
Proof. exact (@lem4814215 _110859 s x). Qed.
Lemma lem4814217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814218 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term58 _110859 x s) = (term59 _110859 s x).
Proof. exact (MK_COMB (@lem4814217) (@lem4814216 _110859 s x)). Qed.
Lemma lem4814220 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814221 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814220 _110859 P x). Qed.
Lemma lem4814222 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (@IN _110859 x t) = (t x).
Proof. exact (@lem4814221 _110859 t x). Qed.
Lemma lem4814223 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814224 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term78 _110859 x t) = (term79 _110859 t x).
Proof. exact (MK_COMB (@lem4814223) (@lem4814222 _110859 t x)). Qed.
Lemma lem4814225 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term77 _110859 s x t) = (term80 _110859 s t x).
Proof. exact (MK_COMB (@lem4814218 _110859 s x) (@lem4814224 _110859 t x)). Qed.
Lemma lem4814228 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term76 _110859 x s t) = (term80 _110859 s t x).
Proof. exact (TRANS (@lem4814210 _110859 s x t) (@lem4814225 _110859 s t x)). Qed.
Lemma lem4814229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814230 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term81 _110859 x s t) = (term82 _110859 s t x).
Proof. exact (MK_COMB (@lem4814229) (@lem4814228 _110859 s t x)). Qed.
Lemma lem4814232 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term76 A x s t) = (term77 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem4814233 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (t : _110859 -> Prop) : (term76 _110859 x s t) = (term77 _110859 s x t).
Proof. exact (@lem4814232 _110859 s x t). Qed.
Lemma lem4814234 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (s : _110859 -> Prop) : (term76 _110859 y t s) = (term77 _110859 t y s).
Proof. exact (@lem4814233 _110859 t y s). Qed.
Lemma lem4814238 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814239 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814238 _110859 P x). Qed.
Lemma lem4814240 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (@IN _110859 y t) = (t y).
Proof. exact (@lem4814239 _110859 t y). Qed.
Lemma lem4814241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814242 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term58 _110859 y t) = (term59 _110859 t y).
Proof. exact (MK_COMB (@lem4814241) (@lem4814240 _110859 t y)). Qed.
Lemma lem4814244 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4814245 {_110859 : Type'} (P : _110859 -> Prop) (x : _110859) : (@IN _110859 x P) = (P x).
Proof. exact (@lem4814244 _110859 P x). Qed.
Lemma lem4814246 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (@IN _110859 y s) = (s y).
Proof. exact (@lem4814245 _110859 s y). Qed.
Lemma lem4814247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814248 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term78 _110859 y s) = (term79 _110859 s y).
Proof. exact (MK_COMB (@lem4814247) (@lem4814246 _110859 s y)). Qed.
Lemma lem4814249 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term77 _110859 t y s) = (term80 _110859 t s y).
Proof. exact (MK_COMB (@lem4814242 _110859 t y) (@lem4814248 _110859 s y)). Qed.
Lemma lem4814252 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term76 _110859 y t s) = (term80 _110859 t s y).
Proof. exact (TRANS (@lem4814234 _110859 t y s) (@lem4814249 _110859 t s y)). Qed.
Lemma lem4814253 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term83 _110859 x y t s) = (term84 _110859 x t s y).
Proof. exact (MK_COMB (@lem4814230 _110859 s t x) (@lem4814252 _110859 t s y)). Qed.
Lemma lem4814256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4814257 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term85 _110859 x y t s) = (term86 _110859 x t s y).
Proof. exact (MK_COMB (@lem4814256) (@lem4814253 _110859 x t s y)). Qed.
Lemma lem4814260 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) : (term87 _110859 R y x) = (term87 _110859 R y x).
Proof. exact (eq_refl (term87 _110859 R y x)). Qed.
Lemma lem4814261 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term88 _110859 t s R y x) = (term89 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4814257 _110859 x t s y) (@lem4814260 _110859 R y x)). Qed.
Lemma lem4814264 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term90 _110859 t s R x) = (term91 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814261 _110859 t s R y x)). Qed.
Lemma lem4814265 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814266 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term92 _110859 t s R x) = (term93 _110859 t s R x).
Proof. exact (MK_COMB (@lem4814265 _110859) (@lem4814264 _110859 t s R x)). Qed.
Lemma lem4814271 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term94 _110859 t s R) = (term95 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814266 _110859 t s R x)). Qed.
Lemma lem4814272 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814273 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term17 _110859 t s R) = (term96 _110859 t s R).
Proof. exact (MK_COMB (@lem4814272 _110859) (@lem4814271 _110859 t s R)). Qed.
Lemma lem4814278 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term19 _110859 t s R) = (term97 _110859 t s R).
Proof. exact (MK_COMB (@lem4814195 _110859 t R) (@lem4814273 _110859 t s R)). Qed.
Lemma lem4814281 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term21 _110859 t s R) = (term98 _110859 t s R).
Proof. exact (MK_COMB (@lem4814136 _110859 s R) (@lem4814278 _110859 t s R)). Qed.
Lemma lem4814284 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term12 _110859 s t R) = (term21 _110859 t s R)) = ((term56 _110859 s t R) = (term98 _110859 t s R)).
Proof. exact (MK_COMB (@lem4814077 _110859 s t R) (@lem4814281 _110859 t s R)). Qed.
Lemma lem4814287 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term23 _110859 s R) = (term99 _110859 s R).
Proof. exact (fun_ext (fun t : _110859 -> Prop => @lem4814284 _110859 t s R)). Qed.
Lemma lem4814288 {_110859 : Type'} : (@all (_110859 -> Prop)) = (@all (_110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> Prop))). Qed.
Lemma lem4814289 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term25 _110859 s R) = (term100 _110859 s R).
Proof. exact (MK_COMB (@lem4814288 _110859) (@lem4814287 _110859 s R)). Qed.
Lemma lem4814294 {_110859 : Type'} (R : type1402 _110859) : (term27 _110859 R) = (term101 _110859 R).
Proof. exact (fun_ext (fun s : _110859 -> Prop => @lem4814289 _110859 s R)). Qed.
Lemma lem4814295 {_110859 : Type'} : (@all (_110859 -> Prop)) = (@all (_110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> Prop))). Qed.
Lemma lem4814296 {_110859 : Type'} (R : type1402 _110859) : (term29 _110859 R) = (term102 _110859 R).
Proof. exact (MK_COMB (@lem4814295 _110859) (@lem4814294 _110859 R)). Qed.
Lemma lem4814301 {_110859 : Type'} : (term31 _110859) = (term103 _110859).
Proof. exact (fun_ext (fun R : type1402 _110859 => @lem4814296 _110859 R)). Qed.
Lemma lem4814302 {_110859 : Type'} : (@all (_110859 -> _110859 -> Prop)) = (@all (_110859 -> _110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> _110859 -> Prop))). Qed.
Lemma lem4814303 {_110859 : Type'} : (term33 _110859) = (term104 _110859).
Proof. exact (MK_COMB (@lem4814302 _110859) (@lem4814301 _110859)). Qed.
Lemma lem4814308 {_110859 : Type'} : (term104 _110859) = (term33 _110859).
Proof. exact (SYM (@lem4814303 _110859)). Qed.
Lemma lem4814310 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4814311 {_110859 : Type'} : (term104 _110859) = (term106 _110859).
Proof. exact (@lem4814310 (term104 _110859)). Qed.
Lemma lem4814312 {_110859 : Type'} : (term106 _110859) = (term104 _110859).
Proof. exact (SYM (@lem4814311 _110859)). Qed.
Lemma lem4814313 {_110859 : Type'} (h1 : term107 _110859) : term107 _110859.
Proof. exact (h1). Qed.
Lemma lem4814316 {_110859 : Type'} (h1 : term106 _110859) : term106 _110859.
Proof. exact (h1). Qed.
Lemma lem4814317 {_110859 : Type'} : term108 _110859.
Proof. exact (fun h0 : term106 _110859 => @lem4814316 _110859 h0). Qed.
Lemma lem4814318 {_110859 : Type'} (h1 : term108 _110859) : term108 _110859.
Proof. exact (h1). Qed.
Lemma lem4814319 {_110859 : Type'} (h1 : term106 _110859) : term106 _110859.
Proof. exact (h1). Qed.
Lemma lem4814320 {_110859 : Type'} (h1 : term106 _110859) (h2 : term108 _110859) : term106 _110859.
Proof. exact (@lem4814318 _110859 h2 (@lem4814319 _110859 h1)). Qed.
Lemma lem4814321 {_110859 : Type'} (h1 : term106 _110859) : term109 _110859.
Proof. exact (fun h0 : term108 _110859 => @lem4814320 _110859 h1 h0). Qed.
Lemma lem4814322 {_110859 : Type'} (h1 : term108 _110859) : term108 _110859.
Proof. exact (h1). Qed.
Lemma lem4814323 {_110859 : Type'} (h1 : term106 _110859) (h2 : term108 _110859) : term106 _110859.
Proof. exact (@lem4814321 _110859 h1 (@lem4814322 _110859 h2)). Qed.
Lemma lem4814324 {_110859 : Type'} (h1 : term108 _110859) : term108 _110859.
Proof. exact (fun h0 : term106 _110859 => @lem4814323 _110859 h0 h1). Qed.
Lemma lem4814325 {_110859 : Type'} : term110 _110859.
Proof. exact (fun h0 : term108 _110859 => @lem4814324 _110859 h0). Qed.
Lemma lem4814328 {_110859 : Type'} : term108 _110859.
Proof. exact (@lem4814325 _110859 (@lem4814317 _110859)). Qed.
Lemma lem4814329 {_110859 : Type'} : term108 _110859.
Proof. exact (@lem4814328 _110859). Qed.
Lemma lem4814331 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4814332 {_110859 : Type'} : (term106 _110859) = (term111 _110859).
Proof. exact (@lem4814331 (term107 _110859)). Qed.
Lemma lem4814334 (t : Prop) : (term112 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4814335 {_110859 : Type'} : (term111 _110859) = (term104 _110859).
Proof. exact (@lem4814334 (term104 _110859)). Qed.
Lemma lem4814420 {_110859 : Type'} : (term106 _110859) = (term104 _110859).
Proof. exact (TRANS (@lem4814332 _110859) (@lem4814335 _110859)). Qed.
Lemma lem4814445 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term89 _110859 t s R y x) = (term89 _110859 t s R y x).
Proof. exact (eq_refl (term89 _110859 t s R y x)). Qed.
Lemma lem4814446 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term91 _110859 t s R x) = (term91 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814445 _110859 t s R y x)). Qed.
Lemma lem4814447 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814448 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term93 _110859 t s R x) = (term93 _110859 t s R x).
Proof. exact (MK_COMB (@lem4814447 _110859) (@lem4814446 _110859 t s R x)). Qed.
Lemma lem4814449 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term95 _110859 t s R) = (term95 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814448 _110859 t s R x)). Qed.
Lemma lem4814450 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814451 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term96 _110859 t s R) = (term96 _110859 t s R).
Proof. exact (MK_COMB (@lem4814450 _110859) (@lem4814449 _110859 t s R)). Qed.
Lemma lem4814466 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term67 _110859 t R x y) = (term67 _110859 t R x y).
Proof. exact (eq_refl (term67 _110859 t R x y)). Qed.
Lemma lem4814467 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term69 _110859 t R x) = (term69 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814466 _110859 t R x y)). Qed.
Lemma lem4814468 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814469 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term71 _110859 t R x) = (term71 _110859 t R x).
Proof. exact (MK_COMB (@lem4814468 _110859) (@lem4814467 _110859 t R x)). Qed.
Lemma lem4814470 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term73 _110859 t R) = (term73 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814469 _110859 t R x)). Qed.
Lemma lem4814471 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814472 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term74 _110859 t R) = (term74 _110859 t R).
Proof. exact (MK_COMB (@lem4814471 _110859) (@lem4814470 _110859 t R)). Qed.
Lemma lem4814473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814474 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term75 _110859 t R) = (term75 _110859 t R).
Proof. exact (MK_COMB (@lem4814473) (@lem4814472 _110859 t R)). Qed.
Lemma lem4814475 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term97 _110859 t s R) = (term97 _110859 t s R).
Proof. exact (MK_COMB (@lem4814474 _110859 t R) (@lem4814451 _110859 t s R)). Qed.
Lemma lem4814490 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term67 _110859 s R x y) = (term67 _110859 s R x y).
Proof. exact (eq_refl (term67 _110859 s R x y)). Qed.
Lemma lem4814491 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term69 _110859 s R x) = (term69 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814490 _110859 s R x y)). Qed.
Lemma lem4814492 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814493 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term71 _110859 s R x) = (term71 _110859 s R x).
Proof. exact (MK_COMB (@lem4814492 _110859) (@lem4814491 _110859 s R x)). Qed.
Lemma lem4814494 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term73 _110859 s R) = (term73 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814493 _110859 s R x)). Qed.
Lemma lem4814495 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814496 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term74 _110859 s R) = (term74 _110859 s R).
Proof. exact (MK_COMB (@lem4814495 _110859) (@lem4814494 _110859 s R)). Qed.
Lemma lem4814497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814498 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term75 _110859 s R) = (term75 _110859 s R).
Proof. exact (MK_COMB (@lem4814497) (@lem4814496 _110859 s R)). Qed.
Lemma lem4814499 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term98 _110859 t s R) = (term98 _110859 t s R).
Proof. exact (MK_COMB (@lem4814498 _110859 s R) (@lem4814475 _110859 t s R)). Qed.
Lemma lem4814522 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term49 _110859 s t R x y) = (term49 _110859 s t R x y).
Proof. exact (eq_refl (term49 _110859 s t R x y)). Qed.
Lemma lem4814523 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term51 _110859 s t R x) = (term51 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814522 _110859 s t R x y)). Qed.
Lemma lem4814524 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814525 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term53 _110859 s t R x) = (term53 _110859 s t R x).
Proof. exact (MK_COMB (@lem4814524 _110859) (@lem4814523 _110859 s t R x)). Qed.
Lemma lem4814526 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term55 _110859 s t R) = (term55 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814525 _110859 s t R x)). Qed.
Lemma lem4814527 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814528 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term56 _110859 s t R) = (term56 _110859 s t R).
Proof. exact (MK_COMB (@lem4814527 _110859) (@lem4814526 _110859 s t R)). Qed.
Lemma lem4814529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4814530 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term57 _110859 s t R) = (term57 _110859 s t R).
Proof. exact (MK_COMB (@lem4814529) (@lem4814528 _110859 s t R)). Qed.
Lemma lem4814531 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term56 _110859 s t R) = (term98 _110859 t s R)) = ((term56 _110859 s t R) = (term98 _110859 t s R)).
Proof. exact (MK_COMB (@lem4814530 _110859 s t R) (@lem4814499 _110859 t s R)). Qed.
Lemma lem4814532 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term99 _110859 s R) = (term99 _110859 s R).
Proof. exact (fun_ext (fun t : _110859 -> Prop => @lem4814531 _110859 t s R)). Qed.
Lemma lem4814533 {_110859 : Type'} : (@all (_110859 -> Prop)) = (@all (_110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> Prop))). Qed.
Lemma lem4814534 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term100 _110859 s R) = (term100 _110859 s R).
Proof. exact (MK_COMB (@lem4814533 _110859) (@lem4814532 _110859 s R)). Qed.
Lemma lem4814535 {_110859 : Type'} (R : type1402 _110859) : (term101 _110859 R) = (term101 _110859 R).
Proof. exact (fun_ext (fun s : _110859 -> Prop => @lem4814534 _110859 s R)). Qed.
Lemma lem4814536 {_110859 : Type'} : (@all (_110859 -> Prop)) = (@all (_110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> Prop))). Qed.
Lemma lem4814537 {_110859 : Type'} (R : type1402 _110859) : (term102 _110859 R) = (term102 _110859 R).
Proof. exact (MK_COMB (@lem4814536 _110859) (@lem4814535 _110859 R)). Qed.
Lemma lem4814538 {_110859 : Type'} : (term103 _110859) = (term103 _110859).
Proof. exact (fun_ext (fun R : type1402 _110859 => @lem4814537 _110859 R)). Qed.
Lemma lem4814539 {_110859 : Type'} : (@all (_110859 -> _110859 -> Prop)) = (@all (_110859 -> _110859 -> Prop)).
Proof. exact (eq_refl (@all (_110859 -> _110859 -> Prop))). Qed.
Lemma lem4814540 {_110859 : Type'} : (term104 _110859) = (term104 _110859).
Proof. exact (MK_COMB (@lem4814539 _110859) (@lem4814538 _110859)). Qed.
Lemma lem4814645 {_110859 : Type'} : (term106 _110859) = (term104 _110859).
Proof. exact (TRANS (@lem4814420 _110859) (@lem4814540 _110859)). Qed.
Lemma lem4814646 {_110859 : Type'} : (term104 _110859) = (term106 _110859).
Proof. exact (SYM (@lem4814645 _110859)). Qed.
Lemma lem4814648 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4814649 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term56 _110859 s t R) = (term98 _110859 t s R)) = (term113 _110859 t s R).
Proof. exact (@lem4814648 ((term56 _110859 s t R) = (term98 _110859 t s R))). Qed.
Lemma lem4814650 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term113 _110859 t s R) = ((term56 _110859 s t R) = (term98 _110859 t s R)).
Proof. exact (SYM (@lem4814649 _110859 t s R)). Qed.
Lemma lem4814651 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term114 _110859 t s R) : term114 _110859 t s R.
Proof. exact (h1). Qed.
Lemma lem4814660 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term115 _110859 s t x) = (term116 _110859 s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem4814672 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (y : _110859) : (term115 _110859 s t y) = (term116 _110859 s t y).
Proof. exact (@lem17160 (s y) (t y)). Qed.
Lemma lem4814679 {_110859 : Type'} (x : _110859) (y : _110859) : (term117 _110859 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4814680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814681 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (y : _110859) : (term118 _110859 s t y) = (term119 _110859 s t y).
Proof. exact (MK_COMB (@lem4814680) (@lem4814672 _110859 s t y)). Qed.
Lemma lem4814682 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term120 _110859 s t x y) = (term121 _110859 s t x y).
Proof. exact (MK_COMB (@lem4814681 _110859 s t y) (@lem4814679 _110859 x y)). Qed.
Lemma lem4814683 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term122 _110859 s t x y) = (term120 _110859 s t x y).
Proof. exact (@lem17045 (term38 _110859 s t y) (term41 _110859 x y)). Qed.
Lemma lem4814684 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term122 _110859 s t x y) = (term121 _110859 s t x y).
Proof. exact (TRANS (@lem4814683 _110859 s t x y) (@lem4814682 _110859 s t x y)). Qed.
Lemma lem4814688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814689 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term118 _110859 s t x) = (term119 _110859 s t x).
Proof. exact (MK_COMB (@lem4814688) (@lem4814660 _110859 s t x)). Qed.
Lemma lem4814690 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term123 _110859 s t x y) = (term124 _110859 s t x y).
Proof. exact (MK_COMB (@lem4814689 _110859 s t x) (@lem4814684 _110859 s t x y)). Qed.
Lemma lem4814691 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term125 _110859 s t x y) = (term123 _110859 s t x y).
Proof. exact (@lem17045 (term38 _110859 s t x) (term43 _110859 s t x y)). Qed.
Lemma lem4814692 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term125 _110859 s t x y) = (term124 _110859 s t x y).
Proof. exact (TRANS (@lem4814691 _110859 s t x y) (@lem4814690 _110859 s t x y)). Qed.
Lemma lem4814697 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4814702 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term126 _110859 s t R x y) = (term127 _110859 s t R x y).
Proof. exact (@lem17362 (term45 _110859 s t x y) (R x y)). Qed.
Lemma lem4814703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814704 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term128 _110859 s t x y) = (term129 _110859 s t x y).
Proof. exact (MK_COMB (@lem4814703) (@lem4814692 _110859 s t x y)). Qed.
Lemma lem4814705 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term130 _110859 s t R x y) = (term131 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4814704 _110859 s t x y) (@lem4814697 _110859 R x y)). Qed.
Lemma lem4814706 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term49 _110859 s t R x y) = (term130 _110859 s t R x y).
Proof. exact (@lem17265 (term45 _110859 s t x y) (R x y)). Qed.
Lemma lem4814707 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term49 _110859 s t R x y) = (term131 _110859 s t R x y).
Proof. exact (TRANS (@lem4814706 _110859 s t R x y) (@lem4814705 _110859 s t R x y)). Qed.
Lemma lem4814708 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814709 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term134 _110859 s t R x) = (term135 _110859 s t R x).
Proof. exact (@lem4814708 _110859 (term51 _110859 s t R x)). Qed.
Lemma lem4814710 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term136 _110859 s t R x y) = (term49 _110859 s t R x y).
Proof. exact (eq_refl (term136 _110859 s t R x y)). Qed.
Lemma lem4814711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814712 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term137 _110859 s t R x y) = (term126 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4814711) (@lem4814710 _110859 s t R x y)). Qed.
Lemma lem4814713 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term137 _110859 s t R x y) = (term127 _110859 s t R x y).
Proof. exact (TRANS (@lem4814712 _110859 s t R x y) (@lem4814702 _110859 s t R x y)). Qed.
Lemma lem4814714 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term138 _110859 s t R x) = (term139 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814713 _110859 s t R x y)). Qed.
Lemma lem4814715 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814716 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term135 _110859 s t R x) = (term140 _110859 s t R x).
Proof. exact (MK_COMB (@lem4814715 _110859) (@lem4814714 _110859 s t R x)). Qed.
Lemma lem4814717 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term134 _110859 s t R x) = (term140 _110859 s t R x).
Proof. exact (TRANS (@lem4814709 _110859 s t R x) (@lem4814716 _110859 s t R x)). Qed.
Lemma lem4814718 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term51 _110859 s t R x) = (term141 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814707 _110859 s t R x y)). Qed.
Lemma lem4814719 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814720 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term53 _110859 s t R x) = (term142 _110859 s t R x).
Proof. exact (MK_COMB (@lem4814719 _110859) (@lem4814718 _110859 s t R x)). Qed.
Lemma lem4814721 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814722 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term143 _110859 s t R) = (term144 _110859 s t R).
Proof. exact (@lem4814721 _110859 (term55 _110859 s t R)). Qed.
Lemma lem4814723 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term145 _110859 s t R x) = (term53 _110859 s t R x).
Proof. exact (eq_refl (term145 _110859 s t R x)). Qed.
Lemma lem4814724 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814725 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term146 _110859 s t R x) = (term134 _110859 s t R x).
Proof. exact (MK_COMB (@lem4814724) (@lem4814723 _110859 s t R x)). Qed.
Lemma lem4814726 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term146 _110859 s t R x) = (term140 _110859 s t R x).
Proof. exact (TRANS (@lem4814725 _110859 s t R x) (@lem4814717 _110859 s t R x)). Qed.
Lemma lem4814727 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term147 _110859 s t R) = (term148 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814726 _110859 s t R x)). Qed.
Lemma lem4814728 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814729 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term144 _110859 s t R) = (term149 _110859 s t R).
Proof. exact (MK_COMB (@lem4814728 _110859) (@lem4814727 _110859 s t R)). Qed.
Lemma lem4814730 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term143 _110859 s t R) = (term149 _110859 s t R).
Proof. exact (TRANS (@lem4814722 _110859 s t R) (@lem4814729 _110859 s t R)). Qed.
Lemma lem4814731 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term55 _110859 s t R) = (term150 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814720 _110859 s t R x)). Qed.
Lemma lem4814732 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814733 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term56 _110859 s t R) = (term151 _110859 s t R).
Proof. exact (MK_COMB (@lem4814732 _110859) (@lem4814731 _110859 s t R)). Qed.
Lemma lem4814741 {_110859 : Type'} (x : _110859) (y : _110859) : (term117 _110859 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4814743 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term152 _110859 s y) = (term152 _110859 s y).
Proof. exact (eq_refl (term152 _110859 s y)). Qed.
Lemma lem4814744 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term153 _110859 s x y) = (term154 _110859 s x y).
Proof. exact (MK_COMB (@lem4814743 _110859 s y) (@lem4814741 _110859 x y)). Qed.
Lemma lem4814745 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term155 _110859 s x y) = (term153 _110859 s x y).
Proof. exact (@lem17045 (s y) (term41 _110859 x y)). Qed.
Lemma lem4814746 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term155 _110859 s x y) = (term154 _110859 s x y).
Proof. exact (TRANS (@lem4814745 _110859 s x y) (@lem4814744 _110859 s x y)). Qed.
Lemma lem4814751 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term152 _110859 s x) = (term152 _110859 s x).
Proof. exact (eq_refl (term152 _110859 s x)). Qed.
Lemma lem4814752 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term156 _110859 s x y) = (term157 _110859 s x y).
Proof. exact (MK_COMB (@lem4814751 _110859 s x) (@lem4814746 _110859 s x y)). Qed.
Lemma lem4814753 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term158 _110859 s x y) = (term156 _110859 s x y).
Proof. exact (@lem17045 (s x) (term61 _110859 s x y)). Qed.
Lemma lem4814754 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term158 _110859 s x y) = (term157 _110859 s x y).
Proof. exact (TRANS (@lem4814753 _110859 s x y) (@lem4814752 _110859 s x y)). Qed.
Lemma lem4814759 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4814764 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term159 _110859 s R x y) = (term160 _110859 s R x y).
Proof. exact (@lem17362 (term63 _110859 s x y) (R x y)). Qed.
Lemma lem4814765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814766 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term161 _110859 s x y) = (term162 _110859 s x y).
Proof. exact (MK_COMB (@lem4814765) (@lem4814754 _110859 s x y)). Qed.
Lemma lem4814767 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term163 _110859 s R x y) = (term164 _110859 s R x y).
Proof. exact (MK_COMB (@lem4814766 _110859 s x y) (@lem4814759 _110859 R x y)). Qed.
Lemma lem4814768 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term67 _110859 s R x y) = (term163 _110859 s R x y).
Proof. exact (@lem17265 (term63 _110859 s x y) (R x y)). Qed.
Lemma lem4814769 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term67 _110859 s R x y) = (term164 _110859 s R x y).
Proof. exact (TRANS (@lem4814768 _110859 s R x y) (@lem4814767 _110859 s R x y)). Qed.
Lemma lem4814770 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814771 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term165 _110859 s R x) = (term166 _110859 s R x).
Proof. exact (@lem4814770 _110859 (term69 _110859 s R x)). Qed.
Lemma lem4814772 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term167 _110859 s R x y) = (term67 _110859 s R x y).
Proof. exact (eq_refl (term167 _110859 s R x y)). Qed.
Lemma lem4814773 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814774 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term168 _110859 s R x y) = (term159 _110859 s R x y).
Proof. exact (MK_COMB (@lem4814773) (@lem4814772 _110859 s R x y)). Qed.
Lemma lem4814775 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term168 _110859 s R x y) = (term160 _110859 s R x y).
Proof. exact (TRANS (@lem4814774 _110859 s R x y) (@lem4814764 _110859 s R x y)). Qed.
Lemma lem4814776 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term169 _110859 s R x) = (term170 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814775 _110859 s R x y)). Qed.
Lemma lem4814777 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814778 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term166 _110859 s R x) = (term171 _110859 s R x).
Proof. exact (MK_COMB (@lem4814777 _110859) (@lem4814776 _110859 s R x)). Qed.
Lemma lem4814779 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term165 _110859 s R x) = (term171 _110859 s R x).
Proof. exact (TRANS (@lem4814771 _110859 s R x) (@lem4814778 _110859 s R x)). Qed.
Lemma lem4814780 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term69 _110859 s R x) = (term172 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814769 _110859 s R x y)). Qed.
Lemma lem4814781 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814782 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term71 _110859 s R x) = (term173 _110859 s R x).
Proof. exact (MK_COMB (@lem4814781 _110859) (@lem4814780 _110859 s R x)). Qed.
Lemma lem4814783 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814784 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term174 _110859 s R) = (term175 _110859 s R).
Proof. exact (@lem4814783 _110859 (term73 _110859 s R)). Qed.
Lemma lem4814785 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term176 _110859 s R x) = (term71 _110859 s R x).
Proof. exact (eq_refl (term176 _110859 s R x)). Qed.
Lemma lem4814786 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814787 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term177 _110859 s R x) = (term165 _110859 s R x).
Proof. exact (MK_COMB (@lem4814786) (@lem4814785 _110859 s R x)). Qed.
Lemma lem4814788 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term177 _110859 s R x) = (term171 _110859 s R x).
Proof. exact (TRANS (@lem4814787 _110859 s R x) (@lem4814779 _110859 s R x)). Qed.
Lemma lem4814789 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term178 _110859 s R) = (term179 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814788 _110859 s R x)). Qed.
Lemma lem4814790 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814791 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term175 _110859 s R) = (term180 _110859 s R).
Proof. exact (MK_COMB (@lem4814790 _110859) (@lem4814789 _110859 s R)). Qed.
Lemma lem4814792 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term174 _110859 s R) = (term180 _110859 s R).
Proof. exact (TRANS (@lem4814784 _110859 s R) (@lem4814791 _110859 s R)). Qed.
Lemma lem4814793 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term73 _110859 s R) = (term181 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814782 _110859 s R x)). Qed.
Lemma lem4814794 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814795 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term74 _110859 s R) = (term182 _110859 s R).
Proof. exact (MK_COMB (@lem4814794 _110859) (@lem4814793 _110859 s R)). Qed.
Lemma lem4814803 {_110859 : Type'} (x : _110859) (y : _110859) : (term117 _110859 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4814805 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term152 _110859 t y) = (term152 _110859 t y).
Proof. exact (eq_refl (term152 _110859 t y)). Qed.
Lemma lem4814806 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term153 _110859 t x y) = (term154 _110859 t x y).
Proof. exact (MK_COMB (@lem4814805 _110859 t y) (@lem4814803 _110859 x y)). Qed.
Lemma lem4814807 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term155 _110859 t x y) = (term153 _110859 t x y).
Proof. exact (@lem17045 (t y) (term41 _110859 x y)). Qed.
Lemma lem4814808 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term155 _110859 t x y) = (term154 _110859 t x y).
Proof. exact (TRANS (@lem4814807 _110859 t x y) (@lem4814806 _110859 t x y)). Qed.
Lemma lem4814813 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term152 _110859 t x) = (term152 _110859 t x).
Proof. exact (eq_refl (term152 _110859 t x)). Qed.
Lemma lem4814814 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term156 _110859 t x y) = (term157 _110859 t x y).
Proof. exact (MK_COMB (@lem4814813 _110859 t x) (@lem4814808 _110859 t x y)). Qed.
Lemma lem4814815 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term158 _110859 t x y) = (term156 _110859 t x y).
Proof. exact (@lem17045 (t x) (term61 _110859 t x y)). Qed.
Lemma lem4814816 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term158 _110859 t x y) = (term157 _110859 t x y).
Proof. exact (TRANS (@lem4814815 _110859 t x y) (@lem4814814 _110859 t x y)). Qed.
Lemma lem4814821 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4814826 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term159 _110859 t R x y) = (term160 _110859 t R x y).
Proof. exact (@lem17362 (term63 _110859 t x y) (R x y)). Qed.
Lemma lem4814827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814828 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term161 _110859 t x y) = (term162 _110859 t x y).
Proof. exact (MK_COMB (@lem4814827) (@lem4814816 _110859 t x y)). Qed.
Lemma lem4814829 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term163 _110859 t R x y) = (term164 _110859 t R x y).
Proof. exact (MK_COMB (@lem4814828 _110859 t x y) (@lem4814821 _110859 R x y)). Qed.
Lemma lem4814830 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term67 _110859 t R x y) = (term163 _110859 t R x y).
Proof. exact (@lem17265 (term63 _110859 t x y) (R x y)). Qed.
Lemma lem4814831 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term67 _110859 t R x y) = (term164 _110859 t R x y).
Proof. exact (TRANS (@lem4814830 _110859 t R x y) (@lem4814829 _110859 t R x y)). Qed.
Lemma lem4814832 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814833 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term165 _110859 t R x) = (term166 _110859 t R x).
Proof. exact (@lem4814832 _110859 (term69 _110859 t R x)). Qed.
Lemma lem4814834 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term167 _110859 t R x y) = (term67 _110859 t R x y).
Proof. exact (eq_refl (term167 _110859 t R x y)). Qed.
Lemma lem4814835 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814836 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term168 _110859 t R x y) = (term159 _110859 t R x y).
Proof. exact (MK_COMB (@lem4814835) (@lem4814834 _110859 t R x y)). Qed.
Lemma lem4814837 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term168 _110859 t R x y) = (term160 _110859 t R x y).
Proof. exact (TRANS (@lem4814836 _110859 t R x y) (@lem4814826 _110859 t R x y)). Qed.
Lemma lem4814838 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term169 _110859 t R x) = (term170 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814837 _110859 t R x y)). Qed.
Lemma lem4814839 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814840 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term166 _110859 t R x) = (term171 _110859 t R x).
Proof. exact (MK_COMB (@lem4814839 _110859) (@lem4814838 _110859 t R x)). Qed.
Lemma lem4814841 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term165 _110859 t R x) = (term171 _110859 t R x).
Proof. exact (TRANS (@lem4814833 _110859 t R x) (@lem4814840 _110859 t R x)). Qed.
Lemma lem4814842 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term69 _110859 t R x) = (term172 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814831 _110859 t R x y)). Qed.
Lemma lem4814843 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814844 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term71 _110859 t R x) = (term173 _110859 t R x).
Proof. exact (MK_COMB (@lem4814843 _110859) (@lem4814842 _110859 t R x)). Qed.
Lemma lem4814845 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814846 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term174 _110859 t R) = (term175 _110859 t R).
Proof. exact (@lem4814845 _110859 (term73 _110859 t R)). Qed.
Lemma lem4814847 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term176 _110859 t R x) = (term71 _110859 t R x).
Proof. exact (eq_refl (term176 _110859 t R x)). Qed.
Lemma lem4814848 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814849 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term177 _110859 t R x) = (term165 _110859 t R x).
Proof. exact (MK_COMB (@lem4814848) (@lem4814847 _110859 t R x)). Qed.
Lemma lem4814850 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term177 _110859 t R x) = (term171 _110859 t R x).
Proof. exact (TRANS (@lem4814849 _110859 t R x) (@lem4814841 _110859 t R x)). Qed.
Lemma lem4814851 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term178 _110859 t R) = (term179 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814850 _110859 t R x)). Qed.
Lemma lem4814852 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814853 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term175 _110859 t R) = (term180 _110859 t R).
Proof. exact (MK_COMB (@lem4814852 _110859) (@lem4814851 _110859 t R)). Qed.
Lemma lem4814854 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term174 _110859 t R) = (term180 _110859 t R).
Proof. exact (TRANS (@lem4814846 _110859 t R) (@lem4814853 _110859 t R)). Qed.
Lemma lem4814855 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term73 _110859 t R) = (term181 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814844 _110859 t R x)). Qed.
Lemma lem4814856 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814857 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term74 _110859 t R) = (term182 _110859 t R).
Proof. exact (MK_COMB (@lem4814856 _110859) (@lem4814855 _110859 t R)). Qed.
Lemma lem4814863 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term183 _110859 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4814865 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term152 _110859 s x) = (term152 _110859 s x).
Proof. exact (eq_refl (term152 _110859 s x)). Qed.
Lemma lem4814866 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term184 _110859 s t x) = (term185 _110859 s t x).
Proof. exact (MK_COMB (@lem4814865 _110859 s x) (@lem4814863 _110859 t x)). Qed.
Lemma lem4814867 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term186 _110859 s t x) = (term184 _110859 s t x).
Proof. exact (@lem17045 (s x) (term79 _110859 t x)). Qed.
Lemma lem4814868 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term186 _110859 s t x) = (term185 _110859 s t x).
Proof. exact (TRANS (@lem4814867 _110859 s t x) (@lem4814866 _110859 s t x)). Qed.
Lemma lem4814877 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term183 _110859 s y) = (s y).
Proof. exact (@lem16933 (s y)). Qed.
Lemma lem4814879 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term152 _110859 t y) = (term152 _110859 t y).
Proof. exact (eq_refl (term152 _110859 t y)). Qed.
Lemma lem4814880 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term184 _110859 t s y) = (term185 _110859 t s y).
Proof. exact (MK_COMB (@lem4814879 _110859 t y) (@lem4814877 _110859 s y)). Qed.
Lemma lem4814881 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term186 _110859 t s y) = (term184 _110859 t s y).
Proof. exact (@lem17045 (t y) (term79 _110859 s y)). Qed.
Lemma lem4814882 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term186 _110859 t s y) = (term185 _110859 t s y).
Proof. exact (TRANS (@lem4814881 _110859 t s y) (@lem4814880 _110859 t s y)). Qed.
Lemma lem4814886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814887 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term187 _110859 s t x) = (term188 _110859 s t x).
Proof. exact (MK_COMB (@lem4814886) (@lem4814868 _110859 s t x)). Qed.
Lemma lem4814888 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term189 _110859 x t s y) = (term190 _110859 x t s y).
Proof. exact (MK_COMB (@lem4814887 _110859 s t x) (@lem4814882 _110859 t s y)). Qed.
Lemma lem4814889 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term191 _110859 x t s y) = (term189 _110859 x t s y).
Proof. exact (@lem17045 (term80 _110859 s t x) (term80 _110859 t s y)). Qed.
Lemma lem4814890 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term191 _110859 x t s y) = (term190 _110859 x t s y).
Proof. exact (TRANS (@lem4814889 _110859 x t s y) (@lem4814888 _110859 x t s y)). Qed.
Lemma lem4814902 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) : (term192 _110859 R y x) = (term193 _110859 R y x).
Proof. exact (@lem17045 (R x y) (R y x)). Qed.
Lemma lem4814905 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) : (term87 _110859 R y x) = (term87 _110859 R y x).
Proof. exact (eq_refl (term87 _110859 R y x)). Qed.
Lemma lem4814907 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term194 _110859 x t s y) = (term194 _110859 x t s y).
Proof. exact (eq_refl (term194 _110859 x t s y)). Qed.
Lemma lem4814908 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term195 _110859 t s R y x) = (term196 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4814907 _110859 x t s y) (@lem4814902 _110859 R y x)). Qed.
Lemma lem4814909 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term197 _110859 t s R y x) = (term195 _110859 t s R y x).
Proof. exact (@lem17362 (term84 _110859 x t s y) (term87 _110859 R y x)). Qed.
Lemma lem4814910 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term197 _110859 t s R y x) = (term196 _110859 t s R y x).
Proof. exact (TRANS (@lem4814909 _110859 t s R y x) (@lem4814908 _110859 t s R y x)). Qed.
Lemma lem4814911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814912 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (y : _110859) : (term198 _110859 x t s y) = (term199 _110859 x t s y).
Proof. exact (MK_COMB (@lem4814911) (@lem4814890 _110859 x t s y)). Qed.
Lemma lem4814913 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term200 _110859 t s R y x) = (term201 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4814912 _110859 x t s y) (@lem4814905 _110859 R y x)). Qed.
Lemma lem4814914 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term89 _110859 t s R y x) = (term200 _110859 t s R y x).
Proof. exact (@lem17265 (term84 _110859 x t s y) (term87 _110859 R y x)). Qed.
Lemma lem4814915 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term89 _110859 t s R y x) = (term201 _110859 t s R y x).
Proof. exact (TRANS (@lem4814914 _110859 t s R y x) (@lem4814913 _110859 t s R y x)). Qed.
Lemma lem4814916 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814917 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term202 _110859 t s R x) = (term203 _110859 t s R x).
Proof. exact (@lem4814916 _110859 (term91 _110859 t s R x)). Qed.
Lemma lem4814918 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term204 _110859 t s R x y) = (term89 _110859 t s R y x).
Proof. exact (eq_refl (term204 _110859 t s R x y)). Qed.
Lemma lem4814919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814920 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term205 _110859 t s R x y) = (term197 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4814919) (@lem4814918 _110859 t s R y x)). Qed.
Lemma lem4814921 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term205 _110859 t s R x y) = (term196 _110859 t s R y x).
Proof. exact (TRANS (@lem4814920 _110859 t s R y x) (@lem4814910 _110859 t s R y x)). Qed.
Lemma lem4814922 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term206 _110859 t s R x) = (term207 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814921 _110859 t s R y x)). Qed.
Lemma lem4814923 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814924 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term203 _110859 t s R x) = (term208 _110859 t s R x).
Proof. exact (MK_COMB (@lem4814923 _110859) (@lem4814922 _110859 t s R x)). Qed.
Lemma lem4814925 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term202 _110859 t s R x) = (term208 _110859 t s R x).
Proof. exact (TRANS (@lem4814917 _110859 t s R x) (@lem4814924 _110859 t s R x)). Qed.
Lemma lem4814926 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term91 _110859 t s R x) = (term209 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4814915 _110859 t s R y x)). Qed.
Lemma lem4814927 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814928 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term93 _110859 t s R x) = (term210 _110859 t s R x).
Proof. exact (MK_COMB (@lem4814927 _110859) (@lem4814926 _110859 t s R x)). Qed.
Lemma lem4814929 {_110859 : Type'} (P : _110859 -> Prop) : (term132 _110859 P) = (term133 _110859 P).
Proof. exact (@lem18392 _110859 P). Qed.
Lemma lem4814930 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term211 _110859 t s R) = (term212 _110859 t s R).
Proof. exact (@lem4814929 _110859 (term95 _110859 t s R)). Qed.
Lemma lem4814931 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term213 _110859 t s R x) = (term93 _110859 t s R x).
Proof. exact (eq_refl (term213 _110859 t s R x)). Qed.
Lemma lem4814932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4814933 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term214 _110859 t s R x) = (term202 _110859 t s R x).
Proof. exact (MK_COMB (@lem4814932) (@lem4814931 _110859 t s R x)). Qed.
Lemma lem4814934 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term214 _110859 t s R x) = (term208 _110859 t s R x).
Proof. exact (TRANS (@lem4814933 _110859 t s R x) (@lem4814925 _110859 t s R x)). Qed.
Lemma lem4814935 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term215 _110859 t s R) = (term216 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814934 _110859 t s R x)). Qed.
Lemma lem4814936 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4814937 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term212 _110859 t s R) = (term217 _110859 t s R).
Proof. exact (MK_COMB (@lem4814936 _110859) (@lem4814935 _110859 t s R)). Qed.
Lemma lem4814938 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term211 _110859 t s R) = (term217 _110859 t s R).
Proof. exact (TRANS (@lem4814930 _110859 t s R) (@lem4814937 _110859 t s R)). Qed.
Lemma lem4814939 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term95 _110859 t s R) = (term218 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4814928 _110859 t s R x)). Qed.
Lemma lem4814940 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4814941 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term96 _110859 t s R) = (term219 _110859 t s R).
Proof. exact (MK_COMB (@lem4814940 _110859) (@lem4814939 _110859 t s R)). Qed.
Lemma lem4814942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814943 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term220 _110859 t R) = (term221 _110859 t R).
Proof. exact (MK_COMB (@lem4814942) (@lem4814854 _110859 t R)). Qed.
Lemma lem4814944 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term222 _110859 t s R) = (term223 _110859 t s R).
Proof. exact (MK_COMB (@lem4814943 _110859 t R) (@lem4814938 _110859 t s R)). Qed.
Lemma lem4814945 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term224 _110859 t s R) = (term222 _110859 t s R).
Proof. exact (@lem17045 (term74 _110859 t R) (term96 _110859 t s R)). Qed.
Lemma lem4814946 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term224 _110859 t s R) = (term223 _110859 t s R).
Proof. exact (TRANS (@lem4814945 _110859 t s R) (@lem4814944 _110859 t s R)). Qed.
Lemma lem4814947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814948 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term75 _110859 t R) = (term225 _110859 t R).
Proof. exact (MK_COMB (@lem4814947) (@lem4814857 _110859 t R)). Qed.
Lemma lem4814949 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term97 _110859 t s R) = (term226 _110859 t s R).
Proof. exact (MK_COMB (@lem4814948 _110859 t R) (@lem4814941 _110859 t s R)). Qed.
Lemma lem4814950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814951 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term220 _110859 s R) = (term221 _110859 s R).
Proof. exact (MK_COMB (@lem4814950) (@lem4814792 _110859 s R)). Qed.
Lemma lem4814952 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term227 _110859 t s R) = (term228 _110859 t s R).
Proof. exact (MK_COMB (@lem4814951 _110859 s R) (@lem4814946 _110859 t s R)). Qed.
Lemma lem4814953 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term229 _110859 t s R) = (term227 _110859 t s R).
Proof. exact (@lem17045 (term74 _110859 s R) (term97 _110859 t s R)). Qed.
Lemma lem4814954 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term229 _110859 t s R) = (term228 _110859 t s R).
Proof. exact (TRANS (@lem4814953 _110859 t s R) (@lem4814952 _110859 t s R)). Qed.
Lemma lem4814955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814956 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term75 _110859 s R) = (term225 _110859 s R).
Proof. exact (MK_COMB (@lem4814955) (@lem4814795 _110859 s R)). Qed.
Lemma lem4814957 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term98 _110859 t s R) = (term230 _110859 t s R).
Proof. exact (MK_COMB (@lem4814956 _110859 s R) (@lem4814949 _110859 t s R)). Qed.
Lemma lem4814958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814959 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term231 _110859 s t R) = (term232 _110859 s t R).
Proof. exact (MK_COMB (@lem4814958) (@lem4814730 _110859 s t R)). Qed.
Lemma lem4814960 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term233 _110859 t s R) = (term234 _110859 t s R).
Proof. exact (MK_COMB (@lem4814959 _110859 s t R) (@lem4814957 _110859 t s R)). Qed.
Lemma lem4814961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4814962 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term235 _110859 s t R) = (term236 _110859 s t R).
Proof. exact (MK_COMB (@lem4814961) (@lem4814733 _110859 s t R)). Qed.
Lemma lem4814963 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term237 _110859 t s R) = (term238 _110859 t s R).
Proof. exact (MK_COMB (@lem4814962 _110859 s t R) (@lem4814954 _110859 t s R)). Qed.
Lemma lem4814964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4814965 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term239 _110859 t s R) = (term240 _110859 t s R).
Proof. exact (MK_COMB (@lem4814964) (@lem4814963 _110859 t s R)). Qed.
Lemma lem4814966 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term241 _110859 t s R) = (term242 _110859 t s R).
Proof. exact (MK_COMB (@lem4814965 _110859 t s R) (@lem4814960 _110859 t s R)). Qed.
Lemma lem4814967 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term114 _110859 t s R) = (term241 _110859 t s R).
Proof. exact (@lem17646 (term56 _110859 s t R) (term98 _110859 t s R)). Qed.
Lemma lem4814968 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term114 _110859 t s R) = (term242 _110859 t s R).
Proof. exact (TRANS (@lem4814967 _110859 t s R) (@lem4814966 _110859 t s R)). Qed.
Lemma lem4815387 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4815388 {_110859 : Type'} (P : _110859 -> Prop) (Q : _110859 -> Prop) : (term243 _110859 P Q) = (term244 _110859 P Q).
Proof. exact (@lem4815387 _110859 P Q). Qed.
Lemma lem4815389 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term245 _110859 t s R) = (term246 _110859 t s R).
Proof. exact (@lem4815388 _110859 (term179 _110859 t R) (term216 _110859 t s R)). Qed.
Lemma lem4815390 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term247 _110859 t R x) = (term171 _110859 t R x).
Proof. exact (eq_refl (term247 _110859 t R x)). Qed.
Lemma lem4815391 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term248 _110859 t R) = (term179 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815390 _110859 t R x)). Qed.
Lemma lem4815392 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815393 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term249 _110859 t R) = (term180 _110859 t R).
Proof. exact (MK_COMB (@lem4815392 _110859) (@lem4815391 _110859 t R)). Qed.
Lemma lem4815394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815395 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term250 _110859 t R) = (term221 _110859 t R).
Proof. exact (MK_COMB (@lem4815394) (@lem4815393 _110859 t R)). Qed.
Lemma lem4815396 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term251 _110859 t s R x) = (term208 _110859 t s R x).
Proof. exact (eq_refl (term251 _110859 t s R x)). Qed.
Lemma lem4815397 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term252 _110859 t s R) = (term216 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815396 _110859 t s R x)). Qed.
Lemma lem4815398 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815399 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term253 _110859 t s R) = (term217 _110859 t s R).
Proof. exact (MK_COMB (@lem4815398 _110859) (@lem4815397 _110859 t s R)). Qed.
Lemma lem4815400 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term245 _110859 t s R) = (term223 _110859 t s R).
Proof. exact (MK_COMB (@lem4815395 _110859 t R) (@lem4815399 _110859 t s R)). Qed.
Lemma lem4815401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815402 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term254 _110859 t s R) = (term255 _110859 t s R).
Proof. exact (MK_COMB (@lem4815401) (@lem4815400 _110859 t s R)). Qed.
Lemma lem4815403 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term247 _110859 t R x) = (term171 _110859 t R x).
Proof. exact (eq_refl (term247 _110859 t R x)). Qed.
Lemma lem4815404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815405 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term256 _110859 t R x) = (term257 _110859 t R x).
Proof. exact (MK_COMB (@lem4815404) (@lem4815403 _110859 t R x)). Qed.
Lemma lem4815406 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term251 _110859 t s R x) = (term208 _110859 t s R x).
Proof. exact (eq_refl (term251 _110859 t s R x)). Qed.
Lemma lem4815407 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term258 _110859 t s R x) = (term259 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815405 _110859 t R x) (@lem4815406 _110859 t s R x)). Qed.
Lemma lem4815408 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term260 _110859 t s R) = (term261 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815407 _110859 t s R x)). Qed.
Lemma lem4815409 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815410 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term246 _110859 t s R) = (term262 _110859 t s R).
Proof. exact (MK_COMB (@lem4815409 _110859) (@lem4815408 _110859 t s R)). Qed.
Lemma lem4815411 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term245 _110859 t s R) = (term246 _110859 t s R)) = ((term223 _110859 t s R) = (term262 _110859 t s R)).
Proof. exact (MK_COMB (@lem4815402 _110859 t s R) (@lem4815410 _110859 t s R)). Qed.
Lemma lem4815412 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term223 _110859 t s R) = (term262 _110859 t s R).
Proof. exact (EQ_MP (@lem4815411 _110859 t s R) (@lem4815389 _110859 t s R)). Qed.
Lemma lem4815414 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4815415 {_110859 : Type'} (P : _110859 -> Prop) (Q : _110859 -> Prop) : (term243 _110859 P Q) = (term244 _110859 P Q).
Proof. exact (@lem4815414 _110859 P Q). Qed.
Lemma lem4815416 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term263 _110859 t s R x) = (term264 _110859 t s R x).
Proof. exact (@lem4815415 _110859 (term170 _110859 t R x) (term207 _110859 t s R x)). Qed.
Lemma lem4815417 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term265 _110859 t R x y) = (term160 _110859 t R x y).
Proof. exact (eq_refl (term265 _110859 t R x y)). Qed.
Lemma lem4815418 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term266 _110859 t R x) = (term170 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815417 _110859 t R x y)). Qed.
Lemma lem4815419 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815420 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term267 _110859 t R x) = (term171 _110859 t R x).
Proof. exact (MK_COMB (@lem4815419 _110859) (@lem4815418 _110859 t R x)). Qed.
Lemma lem4815421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815422 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term268 _110859 t R x) = (term257 _110859 t R x).
Proof. exact (MK_COMB (@lem4815421) (@lem4815420 _110859 t R x)). Qed.
Lemma lem4815423 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term269 _110859 t s R x y) = (term196 _110859 t s R y x).
Proof. exact (eq_refl (term269 _110859 t s R x y)). Qed.
Lemma lem4815424 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term270 _110859 t s R x) = (term207 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815423 _110859 t s R y x)). Qed.
Lemma lem4815425 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815426 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term271 _110859 t s R x) = (term208 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815425 _110859) (@lem4815424 _110859 t s R x)). Qed.
Lemma lem4815427 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term263 _110859 t s R x) = (term259 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815422 _110859 t R x) (@lem4815426 _110859 t s R x)). Qed.
Lemma lem4815428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815429 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term272 _110859 t s R x) = (term273 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815428) (@lem4815427 _110859 t s R x)). Qed.
Lemma lem4815430 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term265 _110859 t R x y) = (term160 _110859 t R x y).
Proof. exact (eq_refl (term265 _110859 t R x y)). Qed.
Lemma lem4815431 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815432 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term274 _110859 t R x y) = (term275 _110859 t R x y).
Proof. exact (MK_COMB (@lem4815431) (@lem4815430 _110859 t R x y)). Qed.
Lemma lem4815433 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term269 _110859 t s R x y) = (term196 _110859 t s R y x).
Proof. exact (eq_refl (term269 _110859 t s R x y)). Qed.
Lemma lem4815434 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term276 _110859 t s R x y) = (term277 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4815432 _110859 t R x y) (@lem4815433 _110859 t s R y x)). Qed.
Lemma lem4815435 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term278 _110859 t s R x) = (term279 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815434 _110859 t s R y x)). Qed.
Lemma lem4815436 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815437 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term264 _110859 t s R x) = (term280 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815436 _110859) (@lem4815435 _110859 t s R x)). Qed.
Lemma lem4815438 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : ((term263 _110859 t s R x) = (term264 _110859 t s R x)) = ((term259 _110859 t s R x) = (term280 _110859 t s R x)).
Proof. exact (MK_COMB (@lem4815429 _110859 t s R x) (@lem4815437 _110859 t s R x)). Qed.
Lemma lem4815439 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term259 _110859 t s R x) = (term280 _110859 t s R x).
Proof. exact (EQ_MP (@lem4815438 _110859 t s R x) (@lem4815416 _110859 t s R x)). Qed.
Lemma lem4815440 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term261 _110859 t s R) = (term281 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815439 _110859 t s R x)). Qed.
Lemma lem4815441 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815442 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term262 _110859 t s R) = (term282 _110859 t s R).
Proof. exact (MK_COMB (@lem4815441 _110859) (@lem4815440 _110859 t s R)). Qed.
Lemma lem4815443 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term223 _110859 t s R) = (term282 _110859 t s R).
Proof. exact (TRANS (@lem4815412 _110859 t s R) (@lem4815442 _110859 t s R)). Qed.
Lemma lem4815444 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term221 _110859 s R) = (term221 _110859 s R).
Proof. exact (eq_refl (term221 _110859 s R)). Qed.
Lemma lem4815445 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term228 _110859 t s R) = (term283 _110859 t s R).
Proof. exact (MK_COMB (@lem4815444 _110859 s R) (@lem4815443 _110859 t s R)). Qed.
Lemma lem4815447 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4815448 {_110859 : Type'} (P : _110859 -> Prop) (Q : _110859 -> Prop) : (term243 _110859 P Q) = (term244 _110859 P Q).
Proof. exact (@lem4815447 _110859 P Q). Qed.
Lemma lem4815449 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term284 _110859 t s R) = (term285 _110859 t s R).
Proof. exact (@lem4815448 _110859 (term179 _110859 s R) (term281 _110859 t s R)). Qed.
Lemma lem4815450 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term247 _110859 s R x) = (term171 _110859 s R x).
Proof. exact (eq_refl (term247 _110859 s R x)). Qed.
Lemma lem4815451 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term248 _110859 s R) = (term179 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815450 _110859 s R x)). Qed.
Lemma lem4815452 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815453 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term249 _110859 s R) = (term180 _110859 s R).
Proof. exact (MK_COMB (@lem4815452 _110859) (@lem4815451 _110859 s R)). Qed.
Lemma lem4815454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815455 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term250 _110859 s R) = (term221 _110859 s R).
Proof. exact (MK_COMB (@lem4815454) (@lem4815453 _110859 s R)). Qed.
Lemma lem4815456 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term286 _110859 t s R x) = (term280 _110859 t s R x).
Proof. exact (eq_refl (term286 _110859 t s R x)). Qed.
Lemma lem4815457 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term287 _110859 t s R) = (term281 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815456 _110859 t s R x)). Qed.
Lemma lem4815458 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815459 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term288 _110859 t s R) = (term282 _110859 t s R).
Proof. exact (MK_COMB (@lem4815458 _110859) (@lem4815457 _110859 t s R)). Qed.
Lemma lem4815460 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term284 _110859 t s R) = (term283 _110859 t s R).
Proof. exact (MK_COMB (@lem4815455 _110859 s R) (@lem4815459 _110859 t s R)). Qed.
Lemma lem4815461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815462 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term289 _110859 t s R) = (term290 _110859 t s R).
Proof. exact (MK_COMB (@lem4815461) (@lem4815460 _110859 t s R)). Qed.
Lemma lem4815463 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term247 _110859 s R x) = (term171 _110859 s R x).
Proof. exact (eq_refl (term247 _110859 s R x)). Qed.
Lemma lem4815464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815465 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term256 _110859 s R x) = (term257 _110859 s R x).
Proof. exact (MK_COMB (@lem4815464) (@lem4815463 _110859 s R x)). Qed.
Lemma lem4815466 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term286 _110859 t s R x) = (term280 _110859 t s R x).
Proof. exact (eq_refl (term286 _110859 t s R x)). Qed.
Lemma lem4815467 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term291 _110859 t s R x) = (term292 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815465 _110859 s R x) (@lem4815466 _110859 t s R x)). Qed.
Lemma lem4815468 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term293 _110859 t s R) = (term294 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815467 _110859 t s R x)). Qed.
Lemma lem4815469 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815470 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term285 _110859 t s R) = (term295 _110859 t s R).
Proof. exact (MK_COMB (@lem4815469 _110859) (@lem4815468 _110859 t s R)). Qed.
Lemma lem4815471 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term284 _110859 t s R) = (term285 _110859 t s R)) = ((term283 _110859 t s R) = (term295 _110859 t s R)).
Proof. exact (MK_COMB (@lem4815462 _110859 t s R) (@lem4815470 _110859 t s R)). Qed.
Lemma lem4815472 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term283 _110859 t s R) = (term295 _110859 t s R).
Proof. exact (EQ_MP (@lem4815471 _110859 t s R) (@lem4815449 _110859 t s R)). Qed.
Lemma lem4815474 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4815475 {_110859 : Type'} (P : _110859 -> Prop) (Q : _110859 -> Prop) : (term243 _110859 P Q) = (term244 _110859 P Q).
Proof. exact (@lem4815474 _110859 P Q). Qed.
Lemma lem4815476 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term296 _110859 t s R x) = (term297 _110859 t s R x).
Proof. exact (@lem4815475 _110859 (term170 _110859 s R x) (term279 _110859 t s R x)). Qed.
Lemma lem4815477 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term265 _110859 s R x y) = (term160 _110859 s R x y).
Proof. exact (eq_refl (term265 _110859 s R x y)). Qed.
Lemma lem4815478 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term266 _110859 s R x) = (term170 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815477 _110859 s R x y)). Qed.
Lemma lem4815479 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815480 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term267 _110859 s R x) = (term171 _110859 s R x).
Proof. exact (MK_COMB (@lem4815479 _110859) (@lem4815478 _110859 s R x)). Qed.
Lemma lem4815481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815482 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term268 _110859 s R x) = (term257 _110859 s R x).
Proof. exact (MK_COMB (@lem4815481) (@lem4815480 _110859 s R x)). Qed.
Lemma lem4815483 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term298 _110859 t s R x y) = (term277 _110859 t s R y x).
Proof. exact (eq_refl (term298 _110859 t s R x y)). Qed.
Lemma lem4815484 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term299 _110859 t s R x) = (term279 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815483 _110859 t s R y x)). Qed.
Lemma lem4815485 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815486 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term300 _110859 t s R x) = (term280 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815485 _110859) (@lem4815484 _110859 t s R x)). Qed.
Lemma lem4815487 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term296 _110859 t s R x) = (term292 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815482 _110859 s R x) (@lem4815486 _110859 t s R x)). Qed.
Lemma lem4815488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815489 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term301 _110859 t s R x) = (term302 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815488) (@lem4815487 _110859 t s R x)). Qed.
Lemma lem4815490 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term265 _110859 s R x y) = (term160 _110859 s R x y).
Proof. exact (eq_refl (term265 _110859 s R x y)). Qed.
Lemma lem4815491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815492 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term274 _110859 s R x y) = (term275 _110859 s R x y).
Proof. exact (MK_COMB (@lem4815491) (@lem4815490 _110859 s R x y)). Qed.
Lemma lem4815493 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term298 _110859 t s R x y) = (term277 _110859 t s R y x).
Proof. exact (eq_refl (term298 _110859 t s R x y)). Qed.
Lemma lem4815494 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term303 _110859 t s R x y) = (term304 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4815492 _110859 s R x y) (@lem4815493 _110859 t s R y x)). Qed.
Lemma lem4815495 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term305 _110859 t s R x) = (term306 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815494 _110859 t s R y x)). Qed.
Lemma lem4815496 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815497 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term297 _110859 t s R x) = (term307 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815496 _110859) (@lem4815495 _110859 t s R x)). Qed.
Lemma lem4815498 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : ((term296 _110859 t s R x) = (term297 _110859 t s R x)) = ((term292 _110859 t s R x) = (term307 _110859 t s R x)).
Proof. exact (MK_COMB (@lem4815489 _110859 t s R x) (@lem4815497 _110859 t s R x)). Qed.
Lemma lem4815499 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term292 _110859 t s R x) = (term307 _110859 t s R x).
Proof. exact (EQ_MP (@lem4815498 _110859 t s R x) (@lem4815476 _110859 t s R x)). Qed.
Lemma lem4815500 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term294 _110859 t s R) = (term308 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815499 _110859 t s R x)). Qed.
Lemma lem4815501 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815502 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term295 _110859 t s R) = (term309 _110859 t s R).
Proof. exact (MK_COMB (@lem4815501 _110859) (@lem4815500 _110859 t s R)). Qed.
Lemma lem4815503 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term283 _110859 t s R) = (term309 _110859 t s R).
Proof. exact (TRANS (@lem4815472 _110859 t s R) (@lem4815502 _110859 t s R)). Qed.
Lemma lem4815504 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term228 _110859 t s R) = (term309 _110859 t s R).
Proof. exact (TRANS (@lem4815445 _110859 t s R) (@lem4815503 _110859 t s R)). Qed.
Lemma lem4815505 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term236 _110859 s t R) = (term236 _110859 s t R).
Proof. exact (eq_refl (term236 _110859 s t R)). Qed.
Lemma lem4815506 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term238 _110859 t s R) = (term310 _110859 t s R).
Proof. exact (MK_COMB (@lem4815505 _110859 s t R) (@lem4815504 _110859 t s R)). Qed.
Lemma lem4815508 {A : Type'} (P : Prop) (Q : A -> Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4815509 {_110859 : Type'} (P : Prop) (Q : _110859 -> Prop) : (term311 _110859 P Q) = (term312 _110859 P Q).
Proof. exact (@lem4815508 _110859 P Q). Qed.
Lemma lem4815510 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term313 _110859 t s R) = (term314 _110859 t s R).
Proof. exact (@lem4815509 _110859 (term151 _110859 s t R) (term308 _110859 t s R)). Qed.
Lemma lem4815511 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term315 _110859 t s R x) = (term307 _110859 t s R x).
Proof. exact (eq_refl (term315 _110859 t s R x)). Qed.
Lemma lem4815512 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term316 _110859 t s R) = (term308 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815511 _110859 t s R x)). Qed.
Lemma lem4815513 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815514 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term317 _110859 t s R) = (term309 _110859 t s R).
Proof. exact (MK_COMB (@lem4815513 _110859) (@lem4815512 _110859 t s R)). Qed.
Lemma lem4815515 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term236 _110859 s t R) = (term236 _110859 s t R).
Proof. exact (eq_refl (term236 _110859 s t R)). Qed.
Lemma lem4815516 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term313 _110859 t s R) = (term310 _110859 t s R).
Proof. exact (MK_COMB (@lem4815515 _110859 s t R) (@lem4815514 _110859 t s R)). Qed.
Lemma lem4815517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815518 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term318 _110859 t s R) = (term319 _110859 t s R).
Proof. exact (MK_COMB (@lem4815517) (@lem4815516 _110859 t s R)). Qed.
Lemma lem4815519 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term315 _110859 t s R x) = (term307 _110859 t s R x).
Proof. exact (eq_refl (term315 _110859 t s R x)). Qed.
Lemma lem4815520 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term236 _110859 s t R) = (term236 _110859 s t R).
Proof. exact (eq_refl (term236 _110859 s t R)). Qed.
Lemma lem4815521 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term320 _110859 t s R x) = (term321 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815520 _110859 s t R) (@lem4815519 _110859 t s R x)). Qed.
Lemma lem4815522 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term322 _110859 t s R) = (term323 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815521 _110859 t s R x)). Qed.
Lemma lem4815523 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815524 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term314 _110859 t s R) = (term324 _110859 t s R).
Proof. exact (MK_COMB (@lem4815523 _110859) (@lem4815522 _110859 t s R)). Qed.
Lemma lem4815525 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term313 _110859 t s R) = (term314 _110859 t s R)) = ((term310 _110859 t s R) = (term324 _110859 t s R)).
Proof. exact (MK_COMB (@lem4815518 _110859 t s R) (@lem4815524 _110859 t s R)). Qed.
Lemma lem4815526 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term310 _110859 t s R) = (term324 _110859 t s R).
Proof. exact (EQ_MP (@lem4815525 _110859 t s R) (@lem4815510 _110859 t s R)). Qed.
Lemma lem4815528 {A : Type'} (P : Prop) (Q : A -> Prop) : (term311 A P Q) = (term312 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4815529 {_110859 : Type'} (P : Prop) (Q : _110859 -> Prop) : (term311 _110859 P Q) = (term312 _110859 P Q).
Proof. exact (@lem4815528 _110859 P Q). Qed.
Lemma lem4815530 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term325 _110859 t s R x) = (term326 _110859 t s R x).
Proof. exact (@lem4815529 _110859 (term151 _110859 s t R) (term306 _110859 t s R x)). Qed.
Lemma lem4815531 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term327 _110859 t s R x y) = (term304 _110859 t s R y x).
Proof. exact (eq_refl (term327 _110859 t s R x y)). Qed.
Lemma lem4815532 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term328 _110859 t s R x) = (term306 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815531 _110859 t s R y x)). Qed.
Lemma lem4815533 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815534 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term329 _110859 t s R x) = (term307 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815533 _110859) (@lem4815532 _110859 t s R x)). Qed.
Lemma lem4815535 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term236 _110859 s t R) = (term236 _110859 s t R).
Proof. exact (eq_refl (term236 _110859 s t R)). Qed.
Lemma lem4815536 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term325 _110859 t s R x) = (term321 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815535 _110859 s t R) (@lem4815534 _110859 t s R x)). Qed.
Lemma lem4815537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815538 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term330 _110859 t s R x) = (term331 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815537) (@lem4815536 _110859 t s R x)). Qed.
Lemma lem4815539 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term327 _110859 t s R x y) = (term304 _110859 t s R y x).
Proof. exact (eq_refl (term327 _110859 t s R x y)). Qed.
Lemma lem4815540 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term236 _110859 s t R) = (term236 _110859 s t R).
Proof. exact (eq_refl (term236 _110859 s t R)). Qed.
Lemma lem4815541 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term332 _110859 t s R x y) = (term333 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4815540 _110859 s t R) (@lem4815539 _110859 t s R y x)). Qed.
Lemma lem4815542 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term334 _110859 t s R x) = (term335 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815541 _110859 t s R y x)). Qed.
Lemma lem4815543 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815544 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term326 _110859 t s R x) = (term336 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815543 _110859) (@lem4815542 _110859 t s R x)). Qed.
Lemma lem4815545 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : ((term325 _110859 t s R x) = (term326 _110859 t s R x)) = ((term321 _110859 t s R x) = (term336 _110859 t s R x)).
Proof. exact (MK_COMB (@lem4815538 _110859 t s R x) (@lem4815544 _110859 t s R x)). Qed.
Lemma lem4815546 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term321 _110859 t s R x) = (term336 _110859 t s R x).
Proof. exact (EQ_MP (@lem4815545 _110859 t s R x) (@lem4815530 _110859 t s R x)). Qed.
Lemma lem4815547 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term323 _110859 t s R) = (term337 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815546 _110859 t s R x)). Qed.
Lemma lem4815548 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815549 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term324 _110859 t s R) = (term338 _110859 t s R).
Proof. exact (MK_COMB (@lem4815548 _110859) (@lem4815547 _110859 t s R)). Qed.
Lemma lem4815550 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term310 _110859 t s R) = (term338 _110859 t s R).
Proof. exact (TRANS (@lem4815526 _110859 t s R) (@lem4815549 _110859 t s R)). Qed.
Lemma lem4815551 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term238 _110859 t s R) = (term338 _110859 t s R).
Proof. exact (TRANS (@lem4815506 _110859 t s R) (@lem4815550 _110859 t s R)). Qed.
Lemma lem4815552 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815553 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term240 _110859 t s R) = (term339 _110859 t s R).
Proof. exact (MK_COMB (@lem4815552) (@lem4815551 _110859 t s R)). Qed.
Lemma lem4815555 {A : Type'} (P : A -> Prop) (Q : Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4815556 {_110859 : Type'} (P : _110859 -> Prop) (Q : Prop) : (term340 _110859 P Q) = (term341 _110859 P Q).
Proof. exact (@lem4815555 _110859 P Q). Qed.
Lemma lem4815557 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term342 _110859 t s R) = (term343 _110859 t s R).
Proof. exact (@lem4815556 _110859 (term148 _110859 s t R) (term230 _110859 t s R)). Qed.
Lemma lem4815558 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term344 _110859 s t R x) = (term140 _110859 s t R x).
Proof. exact (eq_refl (term344 _110859 s t R x)). Qed.
Lemma lem4815559 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term345 _110859 s t R) = (term148 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815558 _110859 s t R x)). Qed.
Lemma lem4815560 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815561 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term346 _110859 s t R) = (term149 _110859 s t R).
Proof. exact (MK_COMB (@lem4815560 _110859) (@lem4815559 _110859 s t R)). Qed.
Lemma lem4815562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4815563 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term347 _110859 s t R) = (term232 _110859 s t R).
Proof. exact (MK_COMB (@lem4815562) (@lem4815561 _110859 s t R)). Qed.
Lemma lem4815564 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term230 _110859 t s R) = (term230 _110859 t s R).
Proof. exact (eq_refl (term230 _110859 t s R)). Qed.
Lemma lem4815565 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term342 _110859 t s R) = (term234 _110859 t s R).
Proof. exact (MK_COMB (@lem4815563 _110859 s t R) (@lem4815564 _110859 t s R)). Qed.
Lemma lem4815566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815567 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term348 _110859 t s R) = (term349 _110859 t s R).
Proof. exact (MK_COMB (@lem4815566) (@lem4815565 _110859 t s R)). Qed.
Lemma lem4815568 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term344 _110859 s t R x) = (term140 _110859 s t R x).
Proof. exact (eq_refl (term344 _110859 s t R x)). Qed.
Lemma lem4815569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4815570 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term350 _110859 s t R x) = (term351 _110859 s t R x).
Proof. exact (MK_COMB (@lem4815569) (@lem4815568 _110859 s t R x)). Qed.
Lemma lem4815571 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term230 _110859 t s R) = (term230 _110859 t s R).
Proof. exact (eq_refl (term230 _110859 t s R)). Qed.
Lemma lem4815572 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term352 _110859 x t s R) = (term353 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815570 _110859 s t R x) (@lem4815571 _110859 t s R)). Qed.
Lemma lem4815573 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term354 _110859 t s R) = (term355 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815572 _110859 x t s R)). Qed.
Lemma lem4815574 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815575 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term343 _110859 t s R) = (term356 _110859 t s R).
Proof. exact (MK_COMB (@lem4815574 _110859) (@lem4815573 _110859 t s R)). Qed.
Lemma lem4815576 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term342 _110859 t s R) = (term343 _110859 t s R)) = ((term234 _110859 t s R) = (term356 _110859 t s R)).
Proof. exact (MK_COMB (@lem4815567 _110859 t s R) (@lem4815575 _110859 t s R)). Qed.
Lemma lem4815577 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term234 _110859 t s R) = (term356 _110859 t s R).
Proof. exact (EQ_MP (@lem4815576 _110859 t s R) (@lem4815557 _110859 t s R)). Qed.
Lemma lem4815579 {A : Type'} (P : A -> Prop) (Q : Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4815580 {_110859 : Type'} (P : _110859 -> Prop) (Q : Prop) : (term340 _110859 P Q) = (term341 _110859 P Q).
Proof. exact (@lem4815579 _110859 P Q). Qed.
Lemma lem4815581 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term357 _110859 x t s R) = (term358 _110859 x t s R).
Proof. exact (@lem4815580 _110859 (term139 _110859 s t R x) (term230 _110859 t s R)). Qed.
Lemma lem4815582 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term359 _110859 s t R x y) = (term127 _110859 s t R x y).
Proof. exact (eq_refl (term359 _110859 s t R x y)). Qed.
Lemma lem4815583 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term360 _110859 s t R x) = (term139 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815582 _110859 s t R x y)). Qed.
Lemma lem4815584 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815585 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term361 _110859 s t R x) = (term140 _110859 s t R x).
Proof. exact (MK_COMB (@lem4815584 _110859) (@lem4815583 _110859 s t R x)). Qed.
Lemma lem4815586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4815587 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term362 _110859 s t R x) = (term351 _110859 s t R x).
Proof. exact (MK_COMB (@lem4815586) (@lem4815585 _110859 s t R x)). Qed.
Lemma lem4815588 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term230 _110859 t s R) = (term230 _110859 t s R).
Proof. exact (eq_refl (term230 _110859 t s R)). Qed.
Lemma lem4815589 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term357 _110859 x t s R) = (term353 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815587 _110859 s t R x) (@lem4815588 _110859 t s R)). Qed.
Lemma lem4815590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815591 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term363 _110859 x t s R) = (term364 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815590) (@lem4815589 _110859 x t s R)). Qed.
Lemma lem4815592 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term359 _110859 s t R x y) = (term127 _110859 s t R x y).
Proof. exact (eq_refl (term359 _110859 s t R x y)). Qed.
Lemma lem4815593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4815594 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term365 _110859 s t R x y) = (term366 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4815593) (@lem4815592 _110859 s t R x y)). Qed.
Lemma lem4815595 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term230 _110859 t s R) = (term230 _110859 t s R).
Proof. exact (eq_refl (term230 _110859 t s R)). Qed.
Lemma lem4815596 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term367 _110859 x y t s R) = (term368 _110859 x y t s R).
Proof. exact (MK_COMB (@lem4815594 _110859 s t R x y) (@lem4815595 _110859 t s R)). Qed.
Lemma lem4815597 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term369 _110859 x t s R) = (term370 _110859 x t s R).
Proof. exact (fun_ext (fun y : _110859 => @lem4815596 _110859 x y t s R)). Qed.
Lemma lem4815598 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815599 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term358 _110859 x t s R) = (term371 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815598 _110859) (@lem4815597 _110859 x t s R)). Qed.
Lemma lem4815600 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term357 _110859 x t s R) = (term358 _110859 x t s R)) = ((term353 _110859 x t s R) = (term371 _110859 x t s R)).
Proof. exact (MK_COMB (@lem4815591 _110859 x t s R) (@lem4815599 _110859 x t s R)). Qed.
Lemma lem4815601 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term353 _110859 x t s R) = (term371 _110859 x t s R).
Proof. exact (EQ_MP (@lem4815600 _110859 x t s R) (@lem4815581 _110859 x t s R)). Qed.
Lemma lem4815602 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term355 _110859 t s R) = (term372 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815601 _110859 x t s R)). Qed.
Lemma lem4815603 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815604 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term356 _110859 t s R) = (term373 _110859 t s R).
Proof. exact (MK_COMB (@lem4815603 _110859) (@lem4815602 _110859 t s R)). Qed.
Lemma lem4815605 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term234 _110859 t s R) = (term373 _110859 t s R).
Proof. exact (TRANS (@lem4815577 _110859 t s R) (@lem4815604 _110859 t s R)). Qed.
Lemma lem4815606 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term242 _110859 t s R) = (term374 _110859 t s R).
Proof. exact (MK_COMB (@lem4815553 _110859 t s R) (@lem4815605 _110859 t s R)). Qed.
Lemma lem4815608 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4815609 {_110859 : Type'} (P : _110859 -> Prop) (Q : _110859 -> Prop) : (term243 _110859 P Q) = (term244 _110859 P Q).
Proof. exact (@lem4815608 _110859 P Q). Qed.
Lemma lem4815610 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term375 _110859 t s R) = (term376 _110859 t s R).
Proof. exact (@lem4815609 _110859 (term337 _110859 t s R) (term372 _110859 t s R)). Qed.
Lemma lem4815611 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term377 _110859 t s R x) = (term336 _110859 t s R x).
Proof. exact (eq_refl (term377 _110859 t s R x)). Qed.
Lemma lem4815612 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term378 _110859 t s R) = (term337 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815611 _110859 t s R x)). Qed.
Lemma lem4815613 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815614 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term379 _110859 t s R) = (term338 _110859 t s R).
Proof. exact (MK_COMB (@lem4815613 _110859) (@lem4815612 _110859 t s R)). Qed.
Lemma lem4815615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815616 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term380 _110859 t s R) = (term339 _110859 t s R).
Proof. exact (MK_COMB (@lem4815615) (@lem4815614 _110859 t s R)). Qed.
Lemma lem4815617 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term381 _110859 t s R x) = (term371 _110859 x t s R).
Proof. exact (eq_refl (term381 _110859 t s R x)). Qed.
Lemma lem4815618 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term382 _110859 t s R) = (term372 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815617 _110859 x t s R)). Qed.
Lemma lem4815619 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815620 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term383 _110859 t s R) = (term373 _110859 t s R).
Proof. exact (MK_COMB (@lem4815619 _110859) (@lem4815618 _110859 t s R)). Qed.
Lemma lem4815621 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term375 _110859 t s R) = (term374 _110859 t s R).
Proof. exact (MK_COMB (@lem4815616 _110859 t s R) (@lem4815620 _110859 t s R)). Qed.
Lemma lem4815622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815623 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term384 _110859 t s R) = (term385 _110859 t s R).
Proof. exact (MK_COMB (@lem4815622) (@lem4815621 _110859 t s R)). Qed.
Lemma lem4815624 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term377 _110859 t s R x) = (term336 _110859 t s R x).
Proof. exact (eq_refl (term377 _110859 t s R x)). Qed.
Lemma lem4815625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815626 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term386 _110859 t s R x) = (term387 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815625) (@lem4815624 _110859 t s R x)). Qed.
Lemma lem4815627 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term381 _110859 t s R x) = (term371 _110859 x t s R).
Proof. exact (eq_refl (term381 _110859 t s R x)). Qed.
Lemma lem4815628 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term388 _110859 t s R x) = (term389 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815626 _110859 t s R x) (@lem4815627 _110859 x t s R)). Qed.
Lemma lem4815629 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term390 _110859 t s R) = (term391 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815628 _110859 x t s R)). Qed.
Lemma lem4815630 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815631 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term376 _110859 t s R) = (term392 _110859 t s R).
Proof. exact (MK_COMB (@lem4815630 _110859) (@lem4815629 _110859 t s R)). Qed.
Lemma lem4815632 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term375 _110859 t s R) = (term376 _110859 t s R)) = ((term374 _110859 t s R) = (term392 _110859 t s R)).
Proof. exact (MK_COMB (@lem4815623 _110859 t s R) (@lem4815631 _110859 t s R)). Qed.
Lemma lem4815633 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term374 _110859 t s R) = (term392 _110859 t s R).
Proof. exact (EQ_MP (@lem4815632 _110859 t s R) (@lem4815610 _110859 t s R)). Qed.
Lemma lem4815635 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4815636 {_110859 : Type'} (P : _110859 -> Prop) (Q : _110859 -> Prop) : (term243 _110859 P Q) = (term244 _110859 P Q).
Proof. exact (@lem4815635 _110859 P Q). Qed.
Lemma lem4815637 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term393 _110859 x t s R) = (term394 _110859 x t s R).
Proof. exact (@lem4815636 _110859 (term335 _110859 t s R x) (term370 _110859 x t s R)). Qed.
Lemma lem4815638 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term395 _110859 t s R x y) = (term333 _110859 t s R y x).
Proof. exact (eq_refl (term395 _110859 t s R x y)). Qed.
Lemma lem4815639 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term396 _110859 t s R x) = (term335 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815638 _110859 t s R y x)). Qed.
Lemma lem4815640 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815641 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term397 _110859 t s R x) = (term336 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815640 _110859) (@lem4815639 _110859 t s R x)). Qed.
Lemma lem4815642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815643 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term398 _110859 t s R x) = (term387 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815642) (@lem4815641 _110859 t s R x)). Qed.
Lemma lem4815644 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term399 _110859 x t s R y) = (term368 _110859 x y t s R).
Proof. exact (eq_refl (term399 _110859 x t s R y)). Qed.
Lemma lem4815645 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term400 _110859 x t s R) = (term370 _110859 x t s R).
Proof. exact (fun_ext (fun y : _110859 => @lem4815644 _110859 x y t s R)). Qed.
Lemma lem4815646 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815647 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term401 _110859 x t s R) = (term371 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815646 _110859) (@lem4815645 _110859 x t s R)). Qed.
Lemma lem4815648 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term393 _110859 x t s R) = (term389 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815643 _110859 t s R x) (@lem4815647 _110859 x t s R)). Qed.
Lemma lem4815649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4815650 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term402 _110859 x t s R) = (term403 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815649) (@lem4815648 _110859 x t s R)). Qed.
Lemma lem4815651 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term395 _110859 t s R x y) = (term333 _110859 t s R y x).
Proof. exact (eq_refl (term395 _110859 t s R x y)). Qed.
Lemma lem4815652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4815653 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term404 _110859 t s R x y) = (term405 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4815652) (@lem4815651 _110859 t s R y x)). Qed.
Lemma lem4815654 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term399 _110859 x t s R y) = (term368 _110859 x y t s R).
Proof. exact (eq_refl (term399 _110859 x t s R y)). Qed.
Lemma lem4815655 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term406 _110859 x t s R y) = (term407 _110859 x y t s R).
Proof. exact (MK_COMB (@lem4815653 _110859 t s R y x) (@lem4815654 _110859 x y t s R)). Qed.
Lemma lem4815656 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term408 _110859 x t s R) = (term409 _110859 x t s R).
Proof. exact (fun_ext (fun y : _110859 => @lem4815655 _110859 x y t s R)). Qed.
Lemma lem4815657 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815658 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term394 _110859 x t s R) = (term410 _110859 x t s R).
Proof. exact (MK_COMB (@lem4815657 _110859) (@lem4815656 _110859 x t s R)). Qed.
Lemma lem4815659 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : ((term393 _110859 x t s R) = (term394 _110859 x t s R)) = ((term389 _110859 x t s R) = (term410 _110859 x t s R)).
Proof. exact (MK_COMB (@lem4815650 _110859 x t s R) (@lem4815658 _110859 x t s R)). Qed.
Lemma lem4815660 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term389 _110859 x t s R) = (term410 _110859 x t s R).
Proof. exact (EQ_MP (@lem4815659 _110859 x t s R) (@lem4815637 _110859 x t s R)). Qed.
Lemma lem4815661 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term391 _110859 t s R) = (term411 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815660 _110859 x t s R)). Qed.
Lemma lem4815662 {_110859 : Type'} : (@ex _110859) = (@ex _110859).
Proof. exact (eq_refl (@ex _110859)). Qed.
Lemma lem4815663 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term392 _110859 t s R) = (term412 _110859 t s R).
Proof. exact (MK_COMB (@lem4815662 _110859) (@lem4815661 _110859 t s R)). Qed.
Lemma lem4815664 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term374 _110859 t s R) = (term412 _110859 t s R).
Proof. exact (TRANS (@lem4815633 _110859 t s R) (@lem4815663 _110859 t s R)). Qed.
Lemma lem4815666 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term242 _110859 t s R) = (term412 _110859 t s R).
Proof. exact (TRANS (@lem4815606 _110859 t s R) (@lem4815664 _110859 t s R)). Qed.
Lemma lem4815667 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term114 _110859 t s R) = (term412 _110859 t s R).
Proof. exact (TRANS (@lem4814968 _110859 t s R) (@lem4815666 _110859 t s R)). Qed.
Lemma lem4815668 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term114 _110859 t s R) : term412 _110859 t s R.
Proof. exact (EQ_MP (@lem4815667 _110859 t s R) (@lem4814651 _110859 t s R h1)). Qed.
Lemma lem4815669 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term410 _110859 x t s R) : term410 _110859 x t s R.
Proof. exact (h1). Qed.
Lemma lem4815670 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term407 _110859 x y t s R) : term407 _110859 x y t s R.
Proof. exact (h1). Qed.
Lemma lem4815711 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term201 _110859 t s R y x) = (term201 _110859 t s R y x).
Proof. exact (eq_refl (term201 _110859 t s R y x)). Qed.
Lemma lem4815712 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term209 _110859 t s R x) = (term209 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815711 _110859 t s R y x)). Qed.
Lemma lem4815713 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815714 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term210 _110859 t s R x) = (term210 _110859 t s R x).
Proof. exact (MK_COMB (@lem4815713 _110859) (@lem4815712 _110859 t s R x)). Qed.
Lemma lem4815715 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term218 _110859 t s R) = (term218 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815714 _110859 t s R x)). Qed.
Lemma lem4815716 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815717 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term219 _110859 t s R) = (term219 _110859 t s R).
Proof. exact (MK_COMB (@lem4815716 _110859) (@lem4815715 _110859 t s R)). Qed.
Lemma lem4815746 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 t R x y) = (term164 _110859 t R x y).
Proof. exact (eq_refl (term164 _110859 t R x y)). Qed.
Lemma lem4815747 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 t R x) = (term172 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815746 _110859 t R x y)). Qed.
Lemma lem4815748 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815749 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 t R x) = (term173 _110859 t R x).
Proof. exact (MK_COMB (@lem4815748 _110859) (@lem4815747 _110859 t R x)). Qed.
Lemma lem4815750 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 t R) = (term181 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815749 _110859 t R x)). Qed.
Lemma lem4815751 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815752 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 t R) = (term182 _110859 t R).
Proof. exact (MK_COMB (@lem4815751 _110859) (@lem4815750 _110859 t R)). Qed.
Lemma lem4815753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4815754 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term225 _110859 t R) = (term225 _110859 t R).
Proof. exact (MK_COMB (@lem4815753) (@lem4815752 _110859 t R)). Qed.
Lemma lem4815755 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term226 _110859 t s R) = (term226 _110859 t s R).
Proof. exact (MK_COMB (@lem4815754 _110859 t R) (@lem4815717 _110859 t s R)). Qed.
Lemma lem4815784 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 s R x y) = (term164 _110859 s R x y).
Proof. exact (eq_refl (term164 _110859 s R x y)). Qed.
Lemma lem4815785 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 s R x) = (term172 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815784 _110859 s R x y)). Qed.
Lemma lem4815786 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815787 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 s R x) = (term173 _110859 s R x).
Proof. exact (MK_COMB (@lem4815786 _110859) (@lem4815785 _110859 s R x)). Qed.
Lemma lem4815788 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 s R) = (term181 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815787 _110859 s R x)). Qed.
Lemma lem4815789 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815790 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 s R) = (term182 _110859 s R).
Proof. exact (MK_COMB (@lem4815789 _110859) (@lem4815788 _110859 s R)). Qed.
Lemma lem4815791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4815792 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term225 _110859 s R) = (term225 _110859 s R).
Proof. exact (MK_COMB (@lem4815791) (@lem4815790 _110859 s R)). Qed.
Lemma lem4815793 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term230 _110859 t s R) = (term230 _110859 t s R).
Proof. exact (MK_COMB (@lem4815792 _110859 s R) (@lem4815755 _110859 t s R)). Qed.
Lemma lem4815836 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term366 _110859 s t R x y) = (term366 _110859 s t R x y).
Proof. exact (eq_refl (term366 _110859 s t R x y)). Qed.
Lemma lem4815837 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term368 _110859 x y t s R) = (term368 _110859 x y t s R).
Proof. exact (MK_COMB (@lem4815836 _110859 s t R x y) (@lem4815793 _110859 t s R)). Qed.
Lemma lem4815946 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term304 _110859 t s R y x) = (term304 _110859 t s R y x).
Proof. exact (eq_refl (term304 _110859 t s R y x)). Qed.
Lemma lem4815991 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term131 _110859 s t R x y).
Proof. exact (eq_refl (term131 _110859 s t R x y)). Qed.
Lemma lem4815992 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term141 _110859 s t R x) = (term141 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4815991 _110859 s t R x y)). Qed.
Lemma lem4815993 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815994 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term142 _110859 s t R x) = (term142 _110859 s t R x).
Proof. exact (MK_COMB (@lem4815993 _110859) (@lem4815992 _110859 s t R x)). Qed.
Lemma lem4815995 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term150 _110859 s t R) = (term150 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4815994 _110859 s t R x)). Qed.
Lemma lem4815996 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4815997 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term151 _110859 s t R) = (term151 _110859 s t R).
Proof. exact (MK_COMB (@lem4815996 _110859) (@lem4815995 _110859 s t R)). Qed.
Lemma lem4815998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4815999 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term236 _110859 s t R) = (term236 _110859 s t R).
Proof. exact (MK_COMB (@lem4815998) (@lem4815997 _110859 s t R)). Qed.
Lemma lem4816000 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term333 _110859 t s R y x) = (term333 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4815999 _110859 s t R) (@lem4815946 _110859 t s R y x)). Qed.
Lemma lem4816001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4816002 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term405 _110859 t s R y x) = (term405 _110859 t s R y x).
Proof. exact (MK_COMB (@lem4816001) (@lem4816000 _110859 t s R y x)). Qed.
Lemma lem4816003 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term407 _110859 x y t s R) = (term407 _110859 x y t s R).
Proof. exact (MK_COMB (@lem4816002 _110859 t s R y x) (@lem4815837 _110859 x y t s R)). Qed.
Lemma lem4816004 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term407 _110859 x y t s R) : term407 _110859 x y t s R.
Proof. exact (EQ_MP (@lem4816003 _110859 x y t s R) (@lem4815670 _110859 x y t s R h1)). Qed.
Lemma lem4816005 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term333 _110859 t s R y x.
Proof. exact (h1). Qed.
Lemma lem4816006 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term368 _110859 x y t s R.
Proof. exact (h1). Qed.
Lemma lem4816007 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term304 _110859 t s R y x.
Proof. exact (proj2 (@lem4816005 _110859 t s R y x h1)). Qed.
Lemma lem4816008 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term151 _110859 s t R.
Proof. exact (proj1 (@lem4816005 _110859 t s R y x h1)). Qed.
Lemma lem4816009 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term160 _110859 s R x y.
Proof. exact (h1). Qed.
Lemma lem4816010 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term277 _110859 t s R y x) : term277 _110859 t s R y x.
Proof. exact (h1). Qed.
Lemma lem4816012 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term63 _110859 s x y.
Proof. exact (proj1 (@lem4816009 _110859 s R x y h1)). Qed.
Lemma lem4816013 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term61 _110859 s x y.
Proof. exact (proj2 (@lem4816012 _110859 s R x y h1)). Qed.
Lemma lem4816017 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term160 _110859 t R x y.
Proof. exact (h1). Qed.
Lemma lem4816018 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term196 _110859 t s R y x.
Proof. exact (h1). Qed.
Lemma lem4816020 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term63 _110859 t x y.
Proof. exact (proj1 (@lem4816017 _110859 t R x y h1)). Qed.
Lemma lem4816021 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term61 _110859 t x y.
Proof. exact (proj2 (@lem4816020 _110859 t R x y h1)). Qed.
Lemma lem4816025 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term193 _110859 R y x.
Proof. exact (proj2 (@lem4816018 _110859 t s R y x h1)). Qed.
Lemma lem4816026 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term84 _110859 x t s y.
Proof. exact (proj1 (@lem4816018 _110859 t s R y x h1)). Qed.
Lemma lem4816027 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term80 _110859 t s y.
Proof. exact (proj2 (@lem4816026 _110859 t s R y x h1)). Qed.
Lemma lem4816028 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term80 _110859 s t x.
Proof. exact (proj1 (@lem4816026 _110859 t s R y x h1)). Qed.
Lemma lem4816035 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term230 _110859 t s R.
Proof. exact (proj2 (@lem4816006 _110859 x y t s R h1)). Qed.
Lemma lem4816036 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term127 _110859 s t R x y.
Proof. exact (proj1 (@lem4816006 _110859 x y t s R h1)). Qed.
Lemma lem4816037 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term226 _110859 t s R.
Proof. exact (proj2 (@lem4816035 _110859 x y t s R h1)). Qed.
Lemma lem4816038 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 s R.
Proof. exact (proj1 (@lem4816035 _110859 x y t s R h1)). Qed.
Lemma lem4816039 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term219 _110859 t s R.
Proof. exact (proj2 (@lem4816037 _110859 x y t s R h1)). Qed.
Lemma lem4816040 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 t R.
Proof. exact (proj1 (@lem4816037 _110859 x y t s R h1)). Qed.
Lemma lem4816042 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term45 _110859 s t x y.
Proof. exact (proj1 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4816043 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term43 _110859 s t x y.
Proof. exact (proj2 (@lem4816042 _110859 x y t s R h1)). Qed.
Lemma lem4816044 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term38 _110859 s t x.
Proof. exact (proj1 (@lem4816042 _110859 x y t s R h1)). Qed.
Lemma lem4816046 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term38 _110859 s t y.
Proof. exact (proj1 (@lem4816043 _110859 x y t s R h1)). Qed.
Lemma lem4816054 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4816071 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term121 _110859 s t x y) = (term413 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s y) (term79 _110859 t y) (x = y)). Qed.
Lemma lem4816078 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term119 _110859 s t x) = (term119 _110859 s t x).
Proof. exact (eq_refl (term119 _110859 s t x)). Qed.
Lemma lem4816079 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term414 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816078 _110859 s t x) (@lem4816071 _110859 s t x y)). Qed.
Lemma lem4816080 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term415 _110859 s t x y).
Proof. exact (@lem19490 (term154 _110859 s x y) (term116 _110859 s t x) (term154 _110859 t x y)). Qed.
Lemma lem4816087 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term416 _110859 s t x y) = (term417 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 t x y)). Qed.
Lemma lem4816094 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term418 _110859 t s x y) = (term419 _110859 t s x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 s x y)). Qed.
Lemma lem4816095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816096 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term420 _110859 t s x y) = (term421 _110859 t s x y).
Proof. exact (MK_COMB (@lem4816095) (@lem4816094 _110859 t s x y)). Qed.
Lemma lem4816097 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term415 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816096 _110859 t s x y) (@lem4816087 _110859 s t x y)). Qed.
Lemma lem4816098 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816080 _110859 s t x y) (@lem4816097 _110859 s t x y)). Qed.
Lemma lem4816099 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816079 _110859 s t x y) (@lem4816098 _110859 s t x y)). Qed.
Lemma lem4816100 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4816101 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term129 _110859 s t x y) = (term423 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816100) (@lem4816099 _110859 s t x y)). Qed.
Lemma lem4816102 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term424 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816101 _110859 s t x y) (@lem4816054 _110859 R x y)). Qed.
Lemma lem4816103 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term425 _110859 s t R x y).
Proof. exact (@lem19699 (term419 _110859 t s x y) (term417 _110859 s t x y) (R x y)). Qed.
Lemma lem4816110 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term426 _110859 s t R x y) = (term427 _110859 s t R x y).
Proof. exact (@lem19699 (term428 _110859 s t x y) (term157 _110859 t x y) (R x y)). Qed.
Lemma lem4816117 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term429 _110859 t s R x y) = (term430 _110859 t s R x y).
Proof. exact (@lem19699 (term157 _110859 s x y) (term428 _110859 t s x y) (R x y)). Qed.
Lemma lem4816118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816119 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term431 _110859 t s R x y) = (term432 _110859 t s R x y).
Proof. exact (MK_COMB (@lem4816118) (@lem4816117 _110859 t s R x y)). Qed.
Lemma lem4816120 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term425 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816119 _110859 t s R x y) (@lem4816110 _110859 s t R x y)). Qed.
Lemma lem4816121 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816103 _110859 s t R x y) (@lem4816120 _110859 s t R x y)). Qed.
Lemma lem4816122 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816102 _110859 s t R x y) (@lem4816121 _110859 s t R x y)). Qed.
Lemma lem4816123 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term141 _110859 s t R x) = (term434 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816122 _110859 s t R x y)). Qed.
Lemma lem4816124 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816125 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term142 _110859 s t R x) = (term435 _110859 s t R x).
Proof. exact (MK_COMB (@lem4816124 _110859) (@lem4816123 _110859 s t R x)). Qed.
Lemma lem4816126 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term150 _110859 s t R) = (term436 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816125 _110859 s t R x)). Qed.
Lemma lem4816127 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816129 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term151 _110859 s t R) = (term437 _110859 s t R).
Proof. exact (MK_COMB (@lem4816127 _110859) (@lem4816126 _110859 s t R)). Qed.
Lemma lem4816130 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term437 _110859 s t R.
Proof. exact (EQ_MP (@lem4816129 _110859 s t R) (@lem4816008 _110859 t s R y x h1)). Qed.
Lemma lem4816148 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4816165 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term121 _110859 s t x y) = (term413 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s y) (term79 _110859 t y) (x = y)). Qed.
Lemma lem4816172 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term119 _110859 s t x) = (term119 _110859 s t x).
Proof. exact (eq_refl (term119 _110859 s t x)). Qed.
Lemma lem4816173 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term414 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816172 _110859 s t x) (@lem4816165 _110859 s t x y)). Qed.
Lemma lem4816174 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term415 _110859 s t x y).
Proof. exact (@lem19490 (term154 _110859 s x y) (term116 _110859 s t x) (term154 _110859 t x y)). Qed.
Lemma lem4816181 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term416 _110859 s t x y) = (term417 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 t x y)). Qed.
Lemma lem4816188 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term418 _110859 t s x y) = (term419 _110859 t s x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 s x y)). Qed.
Lemma lem4816189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816190 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term420 _110859 t s x y) = (term421 _110859 t s x y).
Proof. exact (MK_COMB (@lem4816189) (@lem4816188 _110859 t s x y)). Qed.
Lemma lem4816191 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term415 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816190 _110859 t s x y) (@lem4816181 _110859 s t x y)). Qed.
Lemma lem4816192 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816174 _110859 s t x y) (@lem4816191 _110859 s t x y)). Qed.
Lemma lem4816193 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816173 _110859 s t x y) (@lem4816192 _110859 s t x y)). Qed.
Lemma lem4816194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4816195 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term129 _110859 s t x y) = (term423 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816194) (@lem4816193 _110859 s t x y)). Qed.
Lemma lem4816196 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term424 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816195 _110859 s t x y) (@lem4816148 _110859 R x y)). Qed.
Lemma lem4816197 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term425 _110859 s t R x y).
Proof. exact (@lem19699 (term419 _110859 t s x y) (term417 _110859 s t x y) (R x y)). Qed.
Lemma lem4816204 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term426 _110859 s t R x y) = (term427 _110859 s t R x y).
Proof. exact (@lem19699 (term428 _110859 s t x y) (term157 _110859 t x y) (R x y)). Qed.
Lemma lem4816211 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term429 _110859 t s R x y) = (term430 _110859 t s R x y).
Proof. exact (@lem19699 (term157 _110859 s x y) (term428 _110859 t s x y) (R x y)). Qed.
Lemma lem4816212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816213 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term431 _110859 t s R x y) = (term432 _110859 t s R x y).
Proof. exact (MK_COMB (@lem4816212) (@lem4816211 _110859 t s R x y)). Qed.
Lemma lem4816214 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term425 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816213 _110859 t s R x y) (@lem4816204 _110859 s t R x y)). Qed.
Lemma lem4816215 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816197 _110859 s t R x y) (@lem4816214 _110859 s t R x y)). Qed.
Lemma lem4816216 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816196 _110859 s t R x y) (@lem4816215 _110859 s t R x y)). Qed.
Lemma lem4816217 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term141 _110859 s t R x) = (term434 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816216 _110859 s t R x y)). Qed.
Lemma lem4816218 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816219 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term142 _110859 s t R x) = (term435 _110859 s t R x).
Proof. exact (MK_COMB (@lem4816218 _110859) (@lem4816217 _110859 s t R x)). Qed.
Lemma lem4816220 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term150 _110859 s t R) = (term436 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816219 _110859 s t R x)). Qed.
Lemma lem4816221 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816223 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term151 _110859 s t R) = (term437 _110859 s t R).
Proof. exact (MK_COMB (@lem4816221 _110859) (@lem4816220 _110859 s t R)). Qed.
Lemma lem4816224 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term437 _110859 s t R.
Proof. exact (EQ_MP (@lem4816223 _110859 s t R) (@lem4816008 _110859 t s R y x h1)). Qed.
Lemma lem4816242 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4816259 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term121 _110859 s t x y) = (term413 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s y) (term79 _110859 t y) (x = y)). Qed.
Lemma lem4816266 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term119 _110859 s t x) = (term119 _110859 s t x).
Proof. exact (eq_refl (term119 _110859 s t x)). Qed.
Lemma lem4816267 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term414 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816266 _110859 s t x) (@lem4816259 _110859 s t x y)). Qed.
Lemma lem4816268 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term415 _110859 s t x y).
Proof. exact (@lem19490 (term154 _110859 s x y) (term116 _110859 s t x) (term154 _110859 t x y)). Qed.
Lemma lem4816275 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term416 _110859 s t x y) = (term417 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 t x y)). Qed.
Lemma lem4816282 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term418 _110859 t s x y) = (term419 _110859 t s x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 s x y)). Qed.
Lemma lem4816283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816284 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term420 _110859 t s x y) = (term421 _110859 t s x y).
Proof. exact (MK_COMB (@lem4816283) (@lem4816282 _110859 t s x y)). Qed.
Lemma lem4816285 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term415 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816284 _110859 t s x y) (@lem4816275 _110859 s t x y)). Qed.
Lemma lem4816286 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816268 _110859 s t x y) (@lem4816285 _110859 s t x y)). Qed.
Lemma lem4816287 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816267 _110859 s t x y) (@lem4816286 _110859 s t x y)). Qed.
Lemma lem4816288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4816289 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term129 _110859 s t x y) = (term423 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816288) (@lem4816287 _110859 s t x y)). Qed.
Lemma lem4816290 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term424 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816289 _110859 s t x y) (@lem4816242 _110859 R x y)). Qed.
Lemma lem4816291 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term425 _110859 s t R x y).
Proof. exact (@lem19699 (term419 _110859 t s x y) (term417 _110859 s t x y) (R x y)). Qed.
Lemma lem4816298 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term426 _110859 s t R x y) = (term427 _110859 s t R x y).
Proof. exact (@lem19699 (term428 _110859 s t x y) (term157 _110859 t x y) (R x y)). Qed.
Lemma lem4816305 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term429 _110859 t s R x y) = (term430 _110859 t s R x y).
Proof. exact (@lem19699 (term157 _110859 s x y) (term428 _110859 t s x y) (R x y)). Qed.
Lemma lem4816306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816307 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term431 _110859 t s R x y) = (term432 _110859 t s R x y).
Proof. exact (MK_COMB (@lem4816306) (@lem4816305 _110859 t s R x y)). Qed.
Lemma lem4816308 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term425 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816307 _110859 t s R x y) (@lem4816298 _110859 s t R x y)). Qed.
Lemma lem4816309 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816291 _110859 s t R x y) (@lem4816308 _110859 s t R x y)). Qed.
Lemma lem4816310 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816290 _110859 s t R x y) (@lem4816309 _110859 s t R x y)). Qed.
Lemma lem4816311 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term141 _110859 s t R x) = (term434 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816310 _110859 s t R x y)). Qed.
Lemma lem4816312 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816313 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term142 _110859 s t R x) = (term435 _110859 s t R x).
Proof. exact (MK_COMB (@lem4816312 _110859) (@lem4816311 _110859 s t R x)). Qed.
Lemma lem4816314 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term150 _110859 s t R) = (term436 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816313 _110859 s t R x)). Qed.
Lemma lem4816315 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816317 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term151 _110859 s t R) = (term437 _110859 s t R).
Proof. exact (MK_COMB (@lem4816315 _110859) (@lem4816314 _110859 s t R)). Qed.
Lemma lem4816318 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term437 _110859 s t R.
Proof. exact (EQ_MP (@lem4816317 _110859 s t R) (@lem4816008 _110859 t s R y x h1)). Qed.
Lemma lem4816338 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term438 _110859 R x y) : term438 _110859 R x y.
Proof. exact (h1). Qed.
Lemma lem4816340 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4816357 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term121 _110859 s t x y) = (term413 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s y) (term79 _110859 t y) (x = y)). Qed.
Lemma lem4816364 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) : (term119 _110859 s t x) = (term119 _110859 s t x).
Proof. exact (eq_refl (term119 _110859 s t x)). Qed.
Lemma lem4816365 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term414 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816364 _110859 s t x) (@lem4816357 _110859 s t x y)). Qed.
Lemma lem4816366 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term415 _110859 s t x y).
Proof. exact (@lem19490 (term154 _110859 s x y) (term116 _110859 s t x) (term154 _110859 t x y)). Qed.
Lemma lem4816373 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term416 _110859 s t x y) = (term417 _110859 s t x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 t x y)). Qed.
Lemma lem4816380 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term418 _110859 t s x y) = (term419 _110859 t s x y).
Proof. exact (@lem19699 (term79 _110859 s x) (term79 _110859 t x) (term154 _110859 s x y)). Qed.
Lemma lem4816381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816382 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (x : _110859) (y : _110859) : (term420 _110859 t s x y) = (term421 _110859 t s x y).
Proof. exact (MK_COMB (@lem4816381) (@lem4816380 _110859 t s x y)). Qed.
Lemma lem4816383 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term415 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816382 _110859 t s x y) (@lem4816373 _110859 s t x y)). Qed.
Lemma lem4816384 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term414 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816366 _110859 s t x y) (@lem4816383 _110859 s t x y)). Qed.
Lemma lem4816385 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term124 _110859 s t x y) = (term422 _110859 s t x y).
Proof. exact (TRANS (@lem4816365 _110859 s t x y) (@lem4816384 _110859 s t x y)). Qed.
Lemma lem4816386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4816387 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (x : _110859) (y : _110859) : (term129 _110859 s t x y) = (term423 _110859 s t x y).
Proof. exact (MK_COMB (@lem4816386) (@lem4816385 _110859 s t x y)). Qed.
Lemma lem4816388 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term424 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816387 _110859 s t x y) (@lem4816340 _110859 R x y)). Qed.
Lemma lem4816389 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term425 _110859 s t R x y).
Proof. exact (@lem19699 (term419 _110859 t s x y) (term417 _110859 s t x y) (R x y)). Qed.
Lemma lem4816396 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term426 _110859 s t R x y) = (term427 _110859 s t R x y).
Proof. exact (@lem19699 (term428 _110859 s t x y) (term157 _110859 t x y) (R x y)). Qed.
Lemma lem4816403 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term429 _110859 t s R x y) = (term430 _110859 t s R x y).
Proof. exact (@lem19699 (term157 _110859 s x y) (term428 _110859 t s x y) (R x y)). Qed.
Lemma lem4816404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4816405 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term431 _110859 t s R x y) = (term432 _110859 t s R x y).
Proof. exact (MK_COMB (@lem4816404) (@lem4816403 _110859 t s R x y)). Qed.
Lemma lem4816406 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term425 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (MK_COMB (@lem4816405 _110859 t s R x y) (@lem4816396 _110859 s t R x y)). Qed.
Lemma lem4816407 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term424 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816389 _110859 s t R x y) (@lem4816406 _110859 s t R x y)). Qed.
Lemma lem4816408 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term131 _110859 s t R x y) = (term433 _110859 s t R x y).
Proof. exact (TRANS (@lem4816388 _110859 s t R x y) (@lem4816407 _110859 s t R x y)). Qed.
Lemma lem4816409 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term141 _110859 s t R x) = (term434 _110859 s t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816408 _110859 s t R x y)). Qed.
Lemma lem4816410 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816411 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term142 _110859 s t R x) = (term435 _110859 s t R x).
Proof. exact (MK_COMB (@lem4816410 _110859) (@lem4816409 _110859 s t R x)). Qed.
Lemma lem4816412 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term150 _110859 s t R) = (term436 _110859 s t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816411 _110859 s t R x)). Qed.
Lemma lem4816413 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816415 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) : (term151 _110859 s t R) = (term437 _110859 s t R).
Proof. exact (MK_COMB (@lem4816413 _110859) (@lem4816412 _110859 s t R)). Qed.
Lemma lem4816416 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term437 _110859 s t R.
Proof. exact (EQ_MP (@lem4816415 _110859 s t R) (@lem4816008 _110859 t s R y x h1)). Qed.
Lemma lem4816436 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) : term438 _110859 R y x.
Proof. exact (h1). Qed.
Lemma lem4816456 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 s R x y) = (term164 _110859 s R x y).
Proof. exact (eq_refl (term164 _110859 s R x y)). Qed.
Lemma lem4816457 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 s R x) = (term172 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816456 _110859 s R x y)). Qed.
Lemma lem4816458 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816459 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 s R x) = (term173 _110859 s R x).
Proof. exact (MK_COMB (@lem4816458 _110859) (@lem4816457 _110859 s R x)). Qed.
Lemma lem4816460 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 s R) = (term181 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816459 _110859 s R x)). Qed.
Lemma lem4816461 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816463 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 s R) = (term182 _110859 s R).
Proof. exact (MK_COMB (@lem4816461 _110859) (@lem4816460 _110859 s R)). Qed.
Lemma lem4816464 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 s R.
Proof. exact (EQ_MP (@lem4816463 _110859 s R) (@lem4816038 _110859 x y t s R h1)). Qed.
Lemma lem4816548 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (h1). Qed.
Lemma lem4816552 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4816572 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 s R x y) = (term164 _110859 s R x y).
Proof. exact (eq_refl (term164 _110859 s R x y)). Qed.
Lemma lem4816573 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 s R x) = (term172 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816572 _110859 s R x y)). Qed.
Lemma lem4816574 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816575 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 s R x) = (term173 _110859 s R x).
Proof. exact (MK_COMB (@lem4816574 _110859) (@lem4816573 _110859 s R x)). Qed.
Lemma lem4816576 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 s R) = (term181 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816575 _110859 s R x)). Qed.
Lemma lem4816577 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816579 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 s R) = (term182 _110859 s R).
Proof. exact (MK_COMB (@lem4816577 _110859) (@lem4816576 _110859 s R)). Qed.
Lemma lem4816580 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 s R.
Proof. exact (EQ_MP (@lem4816579 _110859 s R) (@lem4816038 _110859 x y t s R h1)). Qed.
Lemma lem4816600 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 t R x y) = (term164 _110859 t R x y).
Proof. exact (eq_refl (term164 _110859 t R x y)). Qed.
Lemma lem4816601 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 t R x) = (term172 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816600 _110859 t R x y)). Qed.
Lemma lem4816602 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816603 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 t R x) = (term173 _110859 t R x).
Proof. exact (MK_COMB (@lem4816602 _110859) (@lem4816601 _110859 t R x)). Qed.
Lemma lem4816604 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 t R) = (term181 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816603 _110859 t R x)). Qed.
Lemma lem4816605 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816607 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 t R) = (term182 _110859 t R).
Proof. exact (MK_COMB (@lem4816605 _110859) (@lem4816604 _110859 t R)). Qed.
Lemma lem4816608 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 t R.
Proof. exact (EQ_MP (@lem4816607 _110859 t R) (@lem4816040 _110859 x y t s R h1)). Qed.
Lemma lem4816644 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term201 _110859 t s R y x) = (term439 _110859 t s R y x).
Proof. exact (@lem19490 (R x y) (term190 _110859 x t s y) (R y x)). Qed.
Lemma lem4816645 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term209 _110859 t s R x) = (term440 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816644 _110859 t s R y x)). Qed.
Lemma lem4816646 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816647 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term210 _110859 t s R x) = (term441 _110859 t s R x).
Proof. exact (MK_COMB (@lem4816646 _110859) (@lem4816645 _110859 t s R x)). Qed.
Lemma lem4816648 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term218 _110859 t s R) = (term442 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816647 _110859 t s R x)). Qed.
Lemma lem4816649 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816651 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term219 _110859 t s R) = (term443 _110859 t s R).
Proof. exact (MK_COMB (@lem4816649 _110859) (@lem4816648 _110859 t s R)). Qed.
Lemma lem4816652 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term443 _110859 t s R.
Proof. exact (EQ_MP (@lem4816651 _110859 t s R) (@lem4816039 _110859 x y t s R h1)). Qed.
Lemma lem4816664 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (h1). Qed.
Lemma lem4816668 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4816688 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 s R x y) = (term164 _110859 s R x y).
Proof. exact (eq_refl (term164 _110859 s R x y)). Qed.
Lemma lem4816689 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 s R x) = (term172 _110859 s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816688 _110859 s R x y)). Qed.
Lemma lem4816690 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816691 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 s R x) = (term173 _110859 s R x).
Proof. exact (MK_COMB (@lem4816690 _110859) (@lem4816689 _110859 s R x)). Qed.
Lemma lem4816692 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 s R) = (term181 _110859 s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816691 _110859 s R x)). Qed.
Lemma lem4816693 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816695 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 s R) = (term182 _110859 s R).
Proof. exact (MK_COMB (@lem4816693 _110859) (@lem4816692 _110859 s R)). Qed.
Lemma lem4816696 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 s R.
Proof. exact (EQ_MP (@lem4816695 _110859 s R) (@lem4816038 _110859 x y t s R h1)). Qed.
Lemma lem4816716 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 t R x y) = (term164 _110859 t R x y).
Proof. exact (eq_refl (term164 _110859 t R x y)). Qed.
Lemma lem4816717 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 t R x) = (term172 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816716 _110859 t R x y)). Qed.
Lemma lem4816718 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816719 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 t R x) = (term173 _110859 t R x).
Proof. exact (MK_COMB (@lem4816718 _110859) (@lem4816717 _110859 t R x)). Qed.
Lemma lem4816720 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 t R) = (term181 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816719 _110859 t R x)). Qed.
Lemma lem4816721 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816723 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 t R) = (term182 _110859 t R).
Proof. exact (MK_COMB (@lem4816721 _110859) (@lem4816720 _110859 t R)). Qed.
Lemma lem4816724 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 t R.
Proof. exact (EQ_MP (@lem4816723 _110859 t R) (@lem4816040 _110859 x y t s R h1)). Qed.
Lemma lem4816760 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) : (term201 _110859 t s R y x) = (term439 _110859 t s R y x).
Proof. exact (@lem19490 (R x y) (term190 _110859 x t s y) (R y x)). Qed.
Lemma lem4816761 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term209 _110859 t s R x) = (term440 _110859 t s R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816760 _110859 t s R y x)). Qed.
Lemma lem4816762 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816763 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term210 _110859 t s R x) = (term441 _110859 t s R x).
Proof. exact (MK_COMB (@lem4816762 _110859) (@lem4816761 _110859 t s R x)). Qed.
Lemma lem4816764 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term218 _110859 t s R) = (term442 _110859 t s R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816763 _110859 t s R x)). Qed.
Lemma lem4816765 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816767 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term219 _110859 t s R) = (term443 _110859 t s R).
Proof. exact (MK_COMB (@lem4816765 _110859) (@lem4816764 _110859 t s R)). Qed.
Lemma lem4816768 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term443 _110859 t s R.
Proof. exact (EQ_MP (@lem4816767 _110859 t s R) (@lem4816039 _110859 x y t s R h1)). Qed.
Lemma lem4816780 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (h1). Qed.
Lemma lem4816784 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4816832 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) : (term164 _110859 t R x y) = (term164 _110859 t R x y).
Proof. exact (eq_refl (term164 _110859 t R x y)). Qed.
Lemma lem4816833 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term172 _110859 t R x) = (term172 _110859 t R x).
Proof. exact (fun_ext (fun y : _110859 => @lem4816832 _110859 t R x y)). Qed.
Lemma lem4816834 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816835 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) : (term173 _110859 t R x) = (term173 _110859 t R x).
Proof. exact (MK_COMB (@lem4816834 _110859) (@lem4816833 _110859 t R x)). Qed.
Lemma lem4816836 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term181 _110859 t R) = (term181 _110859 t R).
Proof. exact (fun_ext (fun x : _110859 => @lem4816835 _110859 t R x)). Qed.
Lemma lem4816837 {_110859 : Type'} : (@all _110859) = (@all _110859).
Proof. exact (eq_refl (@all _110859)). Qed.
Lemma lem4816839 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) : (term182 _110859 t R) = (term182 _110859 t R).
Proof. exact (MK_COMB (@lem4816837 _110859) (@lem4816836 _110859 t R)). Qed.
Lemma lem4816840 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term182 _110859 t R.
Proof. exact (EQ_MP (@lem4816839 _110859 t R) (@lem4816040 _110859 x y t s R h1)). Qed.
Lemma lem4816896 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (h1). Qed.
Lemma lem4816900 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4816901 {_110859 : Type'} (_59700 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term444 _110859 s t R _59700.
Proof. exact (@lem4816130 _110859 t s R y x h1 _59700). Qed.
Lemma lem4816902 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) : (term444 _110859 s t R _59700) = (term435 _110859 s t R _59700).
Proof. exact (eq_refl (term444 _110859 s t R _59700)). Qed.
Lemma lem4816903 {_110859 : Type'} (_59700 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term435 _110859 s t R _59700.
Proof. exact (EQ_MP (@lem4816902 _110859 s t R _59700) (@lem4816901 _110859 _59700 t s R y x h1)). Qed.
Lemma lem4816904 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term445 _110859 s t R _59700 _59701.
Proof. exact (@lem4816903 _110859 _59700 t s R y x h1 _59701). Qed.
Lemma lem4816905 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term445 _110859 s t R _59700 _59701) = (term433 _110859 s t R _59700 _59701).
Proof. exact (eq_refl (term445 _110859 s t R _59700 _59701)). Qed.
Lemma lem4816906 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term433 _110859 s t R _59700 _59701.
Proof. exact (EQ_MP (@lem4816905 _110859 s t R _59700 _59701) (@lem4816904 _110859 _59700 _59701 t s R y x h1)). Qed.
Lemma lem4816907 {_110859 : Type'} (_59702 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term444 _110859 s t R _59702.
Proof. exact (@lem4816224 _110859 t s R y x h1 _59702). Qed.
Lemma lem4816908 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) : (term444 _110859 s t R _59702) = (term435 _110859 s t R _59702).
Proof. exact (eq_refl (term444 _110859 s t R _59702)). Qed.
Lemma lem4816909 {_110859 : Type'} (_59702 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term435 _110859 s t R _59702.
Proof. exact (EQ_MP (@lem4816908 _110859 s t R _59702) (@lem4816907 _110859 _59702 t s R y x h1)). Qed.
Lemma lem4816910 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term445 _110859 s t R _59702 _59703.
Proof. exact (@lem4816909 _110859 _59702 t s R y x h1 _59703). Qed.
Lemma lem4816911 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term445 _110859 s t R _59702 _59703) = (term433 _110859 s t R _59702 _59703).
Proof. exact (eq_refl (term445 _110859 s t R _59702 _59703)). Qed.
Lemma lem4816912 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term433 _110859 s t R _59702 _59703.
Proof. exact (EQ_MP (@lem4816911 _110859 s t R _59702 _59703) (@lem4816910 _110859 _59702 _59703 t s R y x h1)). Qed.
Lemma lem4816913 {_110859 : Type'} (_59704 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term444 _110859 s t R _59704.
Proof. exact (@lem4816318 _110859 t s R y x h1 _59704). Qed.
Lemma lem4816914 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) : (term444 _110859 s t R _59704) = (term435 _110859 s t R _59704).
Proof. exact (eq_refl (term444 _110859 s t R _59704)). Qed.
Lemma lem4816915 {_110859 : Type'} (_59704 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term435 _110859 s t R _59704.
Proof. exact (EQ_MP (@lem4816914 _110859 s t R _59704) (@lem4816913 _110859 _59704 t s R y x h1)). Qed.
Lemma lem4816916 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term445 _110859 s t R _59704 _59705.
Proof. exact (@lem4816915 _110859 _59704 t s R y x h1 _59705). Qed.
Lemma lem4816917 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term445 _110859 s t R _59704 _59705) = (term433 _110859 s t R _59704 _59705).
Proof. exact (eq_refl (term445 _110859 s t R _59704 _59705)). Qed.
Lemma lem4816918 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term433 _110859 s t R _59704 _59705.
Proof. exact (EQ_MP (@lem4816917 _110859 s t R _59704 _59705) (@lem4816916 _110859 _59704 _59705 t s R y x h1)). Qed.
Lemma lem4816919 {_110859 : Type'} (_59706 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term444 _110859 s t R _59706.
Proof. exact (@lem4816416 _110859 t s R y x h1 _59706). Qed.
Lemma lem4816920 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) : (term444 _110859 s t R _59706) = (term435 _110859 s t R _59706).
Proof. exact (eq_refl (term444 _110859 s t R _59706)). Qed.
Lemma lem4816921 {_110859 : Type'} (_59706 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term435 _110859 s t R _59706.
Proof. exact (EQ_MP (@lem4816920 _110859 s t R _59706) (@lem4816919 _110859 _59706 t s R y x h1)). Qed.
Lemma lem4816922 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term445 _110859 s t R _59706 _59707.
Proof. exact (@lem4816921 _110859 _59706 t s R y x h1 _59707). Qed.
Lemma lem4816923 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term445 _110859 s t R _59706 _59707) = (term433 _110859 s t R _59706 _59707).
Proof. exact (eq_refl (term445 _110859 s t R _59706 _59707)). Qed.
Lemma lem4816924 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term433 _110859 s t R _59706 _59707.
Proof. exact (EQ_MP (@lem4816923 _110859 s t R _59706 _59707) (@lem4816922 _110859 _59706 _59707 t s R y x h1)). Qed.
Lemma lem4816925 {_110859 : Type'} (_59708 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term446 _110859 s R _59708.
Proof. exact (@lem4816464 _110859 x y t s R h1 _59708). Qed.
Lemma lem4816926 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) : (term446 _110859 s R _59708) = (term173 _110859 s R _59708).
Proof. exact (eq_refl (term446 _110859 s R _59708)). Qed.
Lemma lem4816927 {_110859 : Type'} (_59708 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term173 _110859 s R _59708.
Proof. exact (EQ_MP (@lem4816926 _110859 s R _59708) (@lem4816925 _110859 _59708 x y t s R h1)). Qed.
Lemma lem4816928 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term447 _110859 s R _59708 _59709.
Proof. exact (@lem4816927 _110859 _59708 x y t s R h1 _59709). Qed.
Lemma lem4816929 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term447 _110859 s R _59708 _59709) = (term164 _110859 s R _59708 _59709).
Proof. exact (eq_refl (term447 _110859 s R _59708 _59709)). Qed.
Lemma lem4816930 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term164 _110859 s R _59708 _59709.
Proof. exact (EQ_MP (@lem4816929 _110859 s R _59708 _59709) (@lem4816928 _110859 _59708 _59709 x y t s R h1)). Qed.
Lemma lem4816943 {_110859 : Type'} (_59714 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term446 _110859 s R _59714.
Proof. exact (@lem4816580 _110859 x y t s R h1 _59714). Qed.
Lemma lem4816944 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) : (term446 _110859 s R _59714) = (term173 _110859 s R _59714).
Proof. exact (eq_refl (term446 _110859 s R _59714)). Qed.
Lemma lem4816945 {_110859 : Type'} (_59714 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term173 _110859 s R _59714.
Proof. exact (EQ_MP (@lem4816944 _110859 s R _59714) (@lem4816943 _110859 _59714 x y t s R h1)). Qed.
Lemma lem4816946 {_110859 : Type'} (_59714 : _110859) (_59715 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term447 _110859 s R _59714 _59715.
Proof. exact (@lem4816945 _110859 _59714 x y t s R h1 _59715). Qed.
Lemma lem4816947 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term447 _110859 s R _59714 _59715) = (term164 _110859 s R _59714 _59715).
Proof. exact (eq_refl (term447 _110859 s R _59714 _59715)). Qed.
Lemma lem4816948 {_110859 : Type'} (_59714 : _110859) (_59715 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term164 _110859 s R _59714 _59715.
Proof. exact (EQ_MP (@lem4816947 _110859 s R _59714 _59715) (@lem4816946 _110859 _59714 _59715 x y t s R h1)). Qed.
Lemma lem4816949 {_110859 : Type'} (_59716 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term446 _110859 t R _59716.
Proof. exact (@lem4816608 _110859 x y t s R h1 _59716). Qed.
Lemma lem4816950 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) : (term446 _110859 t R _59716) = (term173 _110859 t R _59716).
Proof. exact (eq_refl (term446 _110859 t R _59716)). Qed.
Lemma lem4816951 {_110859 : Type'} (_59716 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term173 _110859 t R _59716.
Proof. exact (EQ_MP (@lem4816950 _110859 t R _59716) (@lem4816949 _110859 _59716 x y t s R h1)). Qed.
Lemma lem4816952 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term447 _110859 t R _59716 _59717.
Proof. exact (@lem4816951 _110859 _59716 x y t s R h1 _59717). Qed.
Lemma lem4816953 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term447 _110859 t R _59716 _59717) = (term164 _110859 t R _59716 _59717).
Proof. exact (eq_refl (term447 _110859 t R _59716 _59717)). Qed.
Lemma lem4816954 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term164 _110859 t R _59716 _59717.
Proof. exact (EQ_MP (@lem4816953 _110859 t R _59716 _59717) (@lem4816952 _110859 _59716 _59717 x y t s R h1)). Qed.
Lemma lem4816955 {_110859 : Type'} (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term448 _110859 t s R _59718.
Proof. exact (@lem4816652 _110859 x y t s R h1 _59718). Qed.
Lemma lem4816956 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59718 : _110859) : (term448 _110859 t s R _59718) = (term441 _110859 t s R _59718).
Proof. exact (eq_refl (term448 _110859 t s R _59718)). Qed.
Lemma lem4816957 {_110859 : Type'} (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term441 _110859 t s R _59718.
Proof. exact (EQ_MP (@lem4816956 _110859 t s R _59718) (@lem4816955 _110859 _59718 x y t s R h1)). Qed.
Lemma lem4816958 {_110859 : Type'} (_59718 : _110859) (_59719 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term449 _110859 t s R _59718 _59719.
Proof. exact (@lem4816957 _110859 _59718 x y t s R h1 _59719). Qed.
Lemma lem4816959 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term449 _110859 t s R _59718 _59719) = (term439 _110859 t s R _59719 _59718).
Proof. exact (eq_refl (term449 _110859 t s R _59718 _59719)). Qed.
Lemma lem4816960 {_110859 : Type'} (_59719 : _110859) (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term439 _110859 t s R _59719 _59718.
Proof. exact (EQ_MP (@lem4816959 _110859 t s R _59719 _59718) (@lem4816958 _110859 _59718 _59719 x y t s R h1)). Qed.
Lemma lem4816961 {_110859 : Type'} (_59720 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term446 _110859 s R _59720.
Proof. exact (@lem4816696 _110859 x y t s R h1 _59720). Qed.
Lemma lem4816962 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) : (term446 _110859 s R _59720) = (term173 _110859 s R _59720).
Proof. exact (eq_refl (term446 _110859 s R _59720)). Qed.
Lemma lem4816963 {_110859 : Type'} (_59720 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term173 _110859 s R _59720.
Proof. exact (EQ_MP (@lem4816962 _110859 s R _59720) (@lem4816961 _110859 _59720 x y t s R h1)). Qed.
Lemma lem4816964 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term447 _110859 s R _59720 _59721.
Proof. exact (@lem4816963 _110859 _59720 x y t s R h1 _59721). Qed.
Lemma lem4816965 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term447 _110859 s R _59720 _59721) = (term164 _110859 s R _59720 _59721).
Proof. exact (eq_refl (term447 _110859 s R _59720 _59721)). Qed.
Lemma lem4816966 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term164 _110859 s R _59720 _59721.
Proof. exact (EQ_MP (@lem4816965 _110859 s R _59720 _59721) (@lem4816964 _110859 _59720 _59721 x y t s R h1)). Qed.
Lemma lem4816967 {_110859 : Type'} (_59722 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term446 _110859 t R _59722.
Proof. exact (@lem4816724 _110859 x y t s R h1 _59722). Qed.
Lemma lem4816968 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) : (term446 _110859 t R _59722) = (term173 _110859 t R _59722).
Proof. exact (eq_refl (term446 _110859 t R _59722)). Qed.
Lemma lem4816969 {_110859 : Type'} (_59722 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term173 _110859 t R _59722.
Proof. exact (EQ_MP (@lem4816968 _110859 t R _59722) (@lem4816967 _110859 _59722 x y t s R h1)). Qed.
Lemma lem4816970 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term447 _110859 t R _59722 _59723.
Proof. exact (@lem4816969 _110859 _59722 x y t s R h1 _59723). Qed.
Lemma lem4816971 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term447 _110859 t R _59722 _59723) = (term164 _110859 t R _59722 _59723).
Proof. exact (eq_refl (term447 _110859 t R _59722 _59723)). Qed.
Lemma lem4816972 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term164 _110859 t R _59722 _59723.
Proof. exact (EQ_MP (@lem4816971 _110859 t R _59722 _59723) (@lem4816970 _110859 _59722 _59723 x y t s R h1)). Qed.
Lemma lem4816973 {_110859 : Type'} (_59724 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term448 _110859 t s R _59724.
Proof. exact (@lem4816768 _110859 x y t s R h1 _59724). Qed.
Lemma lem4816974 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) : (term448 _110859 t s R _59724) = (term441 _110859 t s R _59724).
Proof. exact (eq_refl (term448 _110859 t s R _59724)). Qed.
Lemma lem4816975 {_110859 : Type'} (_59724 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term441 _110859 t s R _59724.
Proof. exact (EQ_MP (@lem4816974 _110859 t s R _59724) (@lem4816973 _110859 _59724 x y t s R h1)). Qed.
Lemma lem4816976 {_110859 : Type'} (_59724 : _110859) (_59725 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term449 _110859 t s R _59724 _59725.
Proof. exact (@lem4816975 _110859 _59724 x y t s R h1 _59725). Qed.
Lemma lem4816977 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59725 : _110859) (_59724 : _110859) : (term449 _110859 t s R _59724 _59725) = (term439 _110859 t s R _59725 _59724).
Proof. exact (eq_refl (term449 _110859 t s R _59724 _59725)). Qed.
Lemma lem4816978 {_110859 : Type'} (_59725 : _110859) (_59724 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term439 _110859 t s R _59725 _59724.
Proof. exact (EQ_MP (@lem4816977 _110859 t s R _59725 _59724) (@lem4816976 _110859 _59724 _59725 x y t s R h1)). Qed.
Lemma lem4816985 {_110859 : Type'} (_59728 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term446 _110859 t R _59728.
Proof. exact (@lem4816840 _110859 x y t s R h1 _59728). Qed.
Lemma lem4816986 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) : (term446 _110859 t R _59728) = (term173 _110859 t R _59728).
Proof. exact (eq_refl (term446 _110859 t R _59728)). Qed.
Lemma lem4816987 {_110859 : Type'} (_59728 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term173 _110859 t R _59728.
Proof. exact (EQ_MP (@lem4816986 _110859 t R _59728) (@lem4816985 _110859 _59728 x y t s R h1)). Qed.
Lemma lem4816988 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term447 _110859 t R _59728 _59729.
Proof. exact (@lem4816987 _110859 _59728 x y t s R h1 _59729). Qed.
Lemma lem4816989 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term447 _110859 t R _59728 _59729) = (term164 _110859 t R _59728 _59729).
Proof. exact (eq_refl (term447 _110859 t R _59728 _59729)). Qed.
Lemma lem4816990 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term164 _110859 t R _59728 _59729.
Proof. exact (EQ_MP (@lem4816989 _110859 t R _59728 _59729) (@lem4816988 _110859 _59728 _59729 x y t s R h1)). Qed.
Lemma lem4816998 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term430 _110859 t s R _59700 _59701.
Proof. exact (proj1 (@lem4816906 _110859 _59700 _59701 t s R y x h1)). Qed.
Lemma lem4817002 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term164 _110859 s R _59700 _59701.
Proof. exact (proj1 (@lem4816998 _110859 _59700 _59701 t s R y x h1)). Qed.
Lemma lem4817003 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term427 _110859 s t R _59702 _59703.
Proof. exact (proj2 (@lem4816912 _110859 _59702 _59703 t s R y x h1)). Qed.
Lemma lem4817005 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term164 _110859 t R _59702 _59703.
Proof. exact (proj2 (@lem4817003 _110859 _59702 _59703 t s R y x h1)). Qed.
Lemma lem4817009 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term427 _110859 s t R _59704 _59705.
Proof. exact (proj2 (@lem4816918 _110859 _59704 _59705 t s R y x h1)). Qed.
Lemma lem4817012 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term450 _110859 s t R _59704 _59705.
Proof. exact (proj1 (@lem4817009 _110859 _59704 _59705 t s R y x h1)). Qed.
Lemma lem4817016 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term430 _110859 t s R _59706 _59707.
Proof. exact (proj1 (@lem4816924 _110859 _59706 _59707 t s R y x h1)). Qed.
Lemma lem4817019 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term450 _110859 t s R _59706 _59707.
Proof. exact (proj2 (@lem4817016 _110859 _59706 _59707 t s R y x h1)). Qed.
Lemma lem4817023 {_110859 : Type'} (_59719 : _110859) (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term451 _110859 t s R _59719 _59718.
Proof. exact (proj2 (@lem4816960 _110859 _59719 _59718 x y t s R h1)). Qed.
Lemma lem4817026 {_110859 : Type'} (_59724 : _110859) (_59725 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term452 _110859 t s R _59724 _59725.
Proof. exact (proj1 (@lem4816978 _110859 _59725 _59724 x y t s R h1)). Qed.
Lemma lem4817036 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term41 _110859 x y.
Proof. exact (proj2 (@lem4816013 _110859 s R x y h1)). Qed.
Lemma lem4817076 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term164 _110859 s R _59700 _59701) = (term453 _110859 s R _59700 _59701).
Proof. exact (@lem4813749 (term79 _110859 s _59700) (term154 _110859 s _59700 _59701) (R _59700 _59701)). Qed.
Lemma lem4817083 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term454 _110859 s R _59700 _59701) = (term455 _110859 s R _59700 _59701).
Proof. exact (@lem4813749 (term79 _110859 s _59701) (_59700 = _59701) (R _59700 _59701)). Qed.
Lemma lem4817084 {_110859 : Type'} (s : _110859 -> Prop) (_59700 : _110859) : (term152 _110859 s _59700) = (term152 _110859 s _59700).
Proof. exact (eq_refl (term152 _110859 s _59700)). Qed.
Lemma lem4817087 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term453 _110859 s R _59700 _59701) = (term456 _110859 s R _59700 _59701).
Proof. exact (MK_COMB (@lem4817084 _110859 s _59700) (@lem4817083 _110859 s R _59700 _59701)). Qed.
Lemma lem4817089 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term164 _110859 s R _59700 _59701) = (term456 _110859 s R _59700 _59701).
Proof. exact (TRANS (@lem4817076 _110859 s R _59700 _59701) (@lem4817087 _110859 s R _59700 _59701)). Qed.
Lemma lem4817090 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term456 _110859 s R _59700 _59701.
Proof. exact (EQ_MP (@lem4817089 _110859 s R _59700 _59701) (@lem4817002 _110859 _59700 _59701 t s R y x h1)). Qed.
Lemma lem4817116 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term41 _110859 x y.
Proof. exact (proj2 (@lem4816021 _110859 t R x y h1)). Qed.
Lemma lem4817138 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term164 _110859 t R _59702 _59703) = (term453 _110859 t R _59702 _59703).
Proof. exact (@lem4813749 (term79 _110859 t _59702) (term154 _110859 t _59702 _59703) (R _59702 _59703)). Qed.
Lemma lem4817145 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term454 _110859 t R _59702 _59703) = (term455 _110859 t R _59702 _59703).
Proof. exact (@lem4813749 (term79 _110859 t _59703) (_59702 = _59703) (R _59702 _59703)). Qed.
Lemma lem4817146 {_110859 : Type'} (t : _110859 -> Prop) (_59702 : _110859) : (term152 _110859 t _59702) = (term152 _110859 t _59702).
Proof. exact (eq_refl (term152 _110859 t _59702)). Qed.
Lemma lem4817149 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term453 _110859 t R _59702 _59703) = (term456 _110859 t R _59702 _59703).
Proof. exact (MK_COMB (@lem4817146 _110859 t _59702) (@lem4817145 _110859 t R _59702 _59703)). Qed.
Lemma lem4817151 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term164 _110859 t R _59702 _59703) = (term456 _110859 t R _59702 _59703).
Proof. exact (TRANS (@lem4817138 _110859 t R _59702 _59703) (@lem4817149 _110859 t R _59702 _59703)). Qed.
Lemma lem4817152 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term456 _110859 t R _59702 _59703.
Proof. exact (EQ_MP (@lem4817151 _110859 t R _59702 _59703) (@lem4817005 _110859 _59702 _59703 t s R y x h1)). Qed.
Lemma lem4817198 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term438 _110859 R x y) : term438 _110859 R x y.
Proof. exact (h1). Qed.
Lemma lem4817202 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term450 _110859 s t R _59704 _59705) = (term457 _110859 s t R _59704 _59705).
Proof. exact (@lem4813749 (term79 _110859 s _59704) (term154 _110859 t _59704 _59705) (R _59704 _59705)). Qed.
Lemma lem4817209 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term454 _110859 t R _59704 _59705) = (term455 _110859 t R _59704 _59705).
Proof. exact (@lem4813749 (term79 _110859 t _59705) (_59704 = _59705) (R _59704 _59705)). Qed.
Lemma lem4817210 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) : (term152 _110859 s _59704) = (term152 _110859 s _59704).
Proof. exact (eq_refl (term152 _110859 s _59704)). Qed.
Lemma lem4817213 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term457 _110859 s t R _59704 _59705) = (term458 _110859 s t R _59704 _59705).
Proof. exact (MK_COMB (@lem4817210 _110859 s _59704) (@lem4817209 _110859 t R _59704 _59705)). Qed.
Lemma lem4817215 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term450 _110859 s t R _59704 _59705) = (term458 _110859 s t R _59704 _59705).
Proof. exact (TRANS (@lem4817202 _110859 s t R _59704 _59705) (@lem4817213 _110859 s t R _59704 _59705)). Qed.
Lemma lem4817216 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term458 _110859 s t R _59704 _59705.
Proof. exact (EQ_MP (@lem4817215 _110859 s t R _59704 _59705) (@lem4817012 _110859 _59704 _59705 t s R y x h1)). Qed.
Lemma lem4817280 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) : term438 _110859 R y x.
Proof. exact (h1). Qed.
Lemma lem4817338 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term450 _110859 t s R _59706 _59707) = (term457 _110859 t s R _59706 _59707).
Proof. exact (@lem4813749 (term79 _110859 t _59706) (term154 _110859 s _59706 _59707) (R _59706 _59707)). Qed.
Lemma lem4817345 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term454 _110859 s R _59706 _59707) = (term455 _110859 s R _59706 _59707).
Proof. exact (@lem4813749 (term79 _110859 s _59707) (_59706 = _59707) (R _59706 _59707)). Qed.
Lemma lem4817346 {_110859 : Type'} (t : _110859 -> Prop) (_59706 : _110859) : (term152 _110859 t _59706) = (term152 _110859 t _59706).
Proof. exact (eq_refl (term152 _110859 t _59706)). Qed.
Lemma lem4817349 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term457 _110859 t s R _59706 _59707) = (term458 _110859 t s R _59706 _59707).
Proof. exact (MK_COMB (@lem4817346 _110859 t _59706) (@lem4817345 _110859 s R _59706 _59707)). Qed.
Lemma lem4817351 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term450 _110859 t s R _59706 _59707) = (term458 _110859 t s R _59706 _59707).
Proof. exact (TRANS (@lem4817338 _110859 t s R _59706 _59707) (@lem4817349 _110859 t s R _59706 _59707)). Qed.
Lemma lem4817352 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term458 _110859 t s R _59706 _59707.
Proof. exact (EQ_MP (@lem4817351 _110859 t s R _59706 _59707) (@lem4817019 _110859 _59706 _59707 t s R y x h1)). Qed.
Lemma lem4817356 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term164 _110859 s R _59708 _59709) = (term453 _110859 s R _59708 _59709).
Proof. exact (@lem4813749 (term79 _110859 s _59708) (term154 _110859 s _59708 _59709) (R _59708 _59709)). Qed.
Lemma lem4817363 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term454 _110859 s R _59708 _59709) = (term455 _110859 s R _59708 _59709).
Proof. exact (@lem4813749 (term79 _110859 s _59709) (_59708 = _59709) (R _59708 _59709)). Qed.
Lemma lem4817364 {_110859 : Type'} (s : _110859 -> Prop) (_59708 : _110859) : (term152 _110859 s _59708) = (term152 _110859 s _59708).
Proof. exact (eq_refl (term152 _110859 s _59708)). Qed.
Lemma lem4817367 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term453 _110859 s R _59708 _59709) = (term456 _110859 s R _59708 _59709).
Proof. exact (MK_COMB (@lem4817364 _110859 s _59708) (@lem4817363 _110859 s R _59708 _59709)). Qed.
Lemma lem4817369 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term164 _110859 s R _59708 _59709) = (term456 _110859 s R _59708 _59709).
Proof. exact (TRANS (@lem4817356 _110859 s R _59708 _59709) (@lem4817367 _110859 s R _59708 _59709)). Qed.
Lemma lem4817370 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term456 _110859 s R _59708 _59709.
Proof. exact (EQ_MP (@lem4817369 _110859 s R _59708 _59709) (@lem4816930 _110859 _59708 _59709 x y t s R h1)). Qed.
Lemma lem4817392 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term41 _110859 x y.
Proof. exact (proj2 (@lem4816043 _110859 x y t s R h1)). Qed.
Lemma lem4817394 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (h1). Qed.
Lemma lem4817396 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4817448 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term164 _110859 s R _59714 _59715) = (term453 _110859 s R _59714 _59715).
Proof. exact (@lem4813749 (term79 _110859 s _59714) (term154 _110859 s _59714 _59715) (R _59714 _59715)). Qed.
Lemma lem4817455 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term454 _110859 s R _59714 _59715) = (term455 _110859 s R _59714 _59715).
Proof. exact (@lem4813749 (term79 _110859 s _59715) (_59714 = _59715) (R _59714 _59715)). Qed.
Lemma lem4817456 {_110859 : Type'} (s : _110859 -> Prop) (_59714 : _110859) : (term152 _110859 s _59714) = (term152 _110859 s _59714).
Proof. exact (eq_refl (term152 _110859 s _59714)). Qed.
Lemma lem4817459 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term453 _110859 s R _59714 _59715) = (term456 _110859 s R _59714 _59715).
Proof. exact (MK_COMB (@lem4817456 _110859 s _59714) (@lem4817455 _110859 s R _59714 _59715)). Qed.
Lemma lem4817461 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term164 _110859 s R _59714 _59715) = (term456 _110859 s R _59714 _59715).
Proof. exact (TRANS (@lem4817448 _110859 s R _59714 _59715) (@lem4817459 _110859 s R _59714 _59715)). Qed.
Lemma lem4817462 {_110859 : Type'} (_59714 : _110859) (_59715 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term456 _110859 s R _59714 _59715.
Proof. exact (EQ_MP (@lem4817461 _110859 s R _59714 _59715) (@lem4816948 _110859 _59714 _59715 x y t s R h1)). Qed.
Lemma lem4817466 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term164 _110859 t R _59716 _59717) = (term453 _110859 t R _59716 _59717).
Proof. exact (@lem4813749 (term79 _110859 t _59716) (term154 _110859 t _59716 _59717) (R _59716 _59717)). Qed.
Lemma lem4817473 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term454 _110859 t R _59716 _59717) = (term455 _110859 t R _59716 _59717).
Proof. exact (@lem4813749 (term79 _110859 t _59717) (_59716 = _59717) (R _59716 _59717)). Qed.
Lemma lem4817474 {_110859 : Type'} (t : _110859 -> Prop) (_59716 : _110859) : (term152 _110859 t _59716) = (term152 _110859 t _59716).
Proof. exact (eq_refl (term152 _110859 t _59716)). Qed.
Lemma lem4817477 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term453 _110859 t R _59716 _59717) = (term456 _110859 t R _59716 _59717).
Proof. exact (MK_COMB (@lem4817474 _110859 t _59716) (@lem4817473 _110859 t R _59716 _59717)). Qed.
Lemma lem4817479 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term164 _110859 t R _59716 _59717) = (term456 _110859 t R _59716 _59717).
Proof. exact (TRANS (@lem4817466 _110859 t R _59716 _59717) (@lem4817477 _110859 t R _59716 _59717)). Qed.
Lemma lem4817480 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term456 _110859 t R _59716 _59717.
Proof. exact (EQ_MP (@lem4817479 _110859 t R _59716 _59717) (@lem4816954 _110859 _59716 _59717 x y t s R h1)). Qed.
Lemma lem4817484 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term41 _110859 x y.
Proof. exact (proj2 (@lem4816043 _110859 x y t s R h1)). Qed.
Lemma lem4817486 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (h1). Qed.
Lemma lem4817488 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4817516 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term451 _110859 t s R _59719 _59718) = (term459 _110859 t s R _59719 _59718).
Proof. exact (@lem4813749 (term185 _110859 s t _59718) (term185 _110859 t s _59719) (R _59719 _59718)). Qed.
Lemma lem4817523 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term460 _110859 t s R _59719 _59718) = (term461 _110859 t s R _59719 _59718).
Proof. exact (@lem4813749 (term79 _110859 t _59719) (s _59719) (R _59719 _59718)). Qed.
Lemma lem4817524 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (_59718 : _110859) : (term188 _110859 s t _59718) = (term188 _110859 s t _59718).
Proof. exact (eq_refl (term188 _110859 s t _59718)). Qed.
Lemma lem4817525 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term459 _110859 t s R _59719 _59718) = (term462 _110859 t s R _59719 _59718).
Proof. exact (MK_COMB (@lem4817524 _110859 s t _59718) (@lem4817523 _110859 t s R _59719 _59718)). Qed.
Lemma lem4817532 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term462 _110859 t s R _59719 _59718) = (term463 _110859 t s R _59719 _59718).
Proof. exact (@lem4813749 (term79 _110859 s _59718) (t _59718) (term461 _110859 t s R _59719 _59718)). Qed.
Lemma lem4817533 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term459 _110859 t s R _59719 _59718) = (term463 _110859 t s R _59719 _59718).
Proof. exact (TRANS (@lem4817525 _110859 t s R _59719 _59718) (@lem4817532 _110859 t s R _59719 _59718)). Qed.
Lemma lem4817535 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term451 _110859 t s R _59719 _59718) = (term463 _110859 t s R _59719 _59718).
Proof. exact (TRANS (@lem4817516 _110859 t s R _59719 _59718) (@lem4817533 _110859 t s R _59719 _59718)). Qed.
Lemma lem4817536 {_110859 : Type'} (_59719 : _110859) (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term463 _110859 t s R _59719 _59718.
Proof. exact (EQ_MP (@lem4817535 _110859 t s R _59719 _59718) (@lem4817023 _110859 _59719 _59718 x y t s R h1)). Qed.
Lemma lem4817540 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term164 _110859 s R _59720 _59721) = (term453 _110859 s R _59720 _59721).
Proof. exact (@lem4813749 (term79 _110859 s _59720) (term154 _110859 s _59720 _59721) (R _59720 _59721)). Qed.
Lemma lem4817547 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term454 _110859 s R _59720 _59721) = (term455 _110859 s R _59720 _59721).
Proof. exact (@lem4813749 (term79 _110859 s _59721) (_59720 = _59721) (R _59720 _59721)). Qed.
Lemma lem4817548 {_110859 : Type'} (s : _110859 -> Prop) (_59720 : _110859) : (term152 _110859 s _59720) = (term152 _110859 s _59720).
Proof. exact (eq_refl (term152 _110859 s _59720)). Qed.
Lemma lem4817551 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term453 _110859 s R _59720 _59721) = (term456 _110859 s R _59720 _59721).
Proof. exact (MK_COMB (@lem4817548 _110859 s _59720) (@lem4817547 _110859 s R _59720 _59721)). Qed.
Lemma lem4817553 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term164 _110859 s R _59720 _59721) = (term456 _110859 s R _59720 _59721).
Proof. exact (TRANS (@lem4817540 _110859 s R _59720 _59721) (@lem4817551 _110859 s R _59720 _59721)). Qed.
Lemma lem4817554 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term456 _110859 s R _59720 _59721.
Proof. exact (EQ_MP (@lem4817553 _110859 s R _59720 _59721) (@lem4816966 _110859 _59720 _59721 x y t s R h1)). Qed.
Lemma lem4817558 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term164 _110859 t R _59722 _59723) = (term453 _110859 t R _59722 _59723).
Proof. exact (@lem4813749 (term79 _110859 t _59722) (term154 _110859 t _59722 _59723) (R _59722 _59723)). Qed.
Lemma lem4817565 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term454 _110859 t R _59722 _59723) = (term455 _110859 t R _59722 _59723).
Proof. exact (@lem4813749 (term79 _110859 t _59723) (_59722 = _59723) (R _59722 _59723)). Qed.
Lemma lem4817566 {_110859 : Type'} (t : _110859 -> Prop) (_59722 : _110859) : (term152 _110859 t _59722) = (term152 _110859 t _59722).
Proof. exact (eq_refl (term152 _110859 t _59722)). Qed.
Lemma lem4817569 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term453 _110859 t R _59722 _59723) = (term456 _110859 t R _59722 _59723).
Proof. exact (MK_COMB (@lem4817566 _110859 t _59722) (@lem4817565 _110859 t R _59722 _59723)). Qed.
Lemma lem4817571 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term164 _110859 t R _59722 _59723) = (term456 _110859 t R _59722 _59723).
Proof. exact (TRANS (@lem4817558 _110859 t R _59722 _59723) (@lem4817569 _110859 t R _59722 _59723)). Qed.
Lemma lem4817572 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term456 _110859 t R _59722 _59723.
Proof. exact (EQ_MP (@lem4817571 _110859 t R _59722 _59723) (@lem4816972 _110859 _59722 _59723 x y t s R h1)). Qed.
Lemma lem4817576 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term41 _110859 x y.
Proof. exact (proj2 (@lem4816043 _110859 x y t s R h1)). Qed.
Lemma lem4817578 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (h1). Qed.
Lemma lem4817580 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4817584 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term452 _110859 t s R _59724 _59725) = (term464 _110859 t s R _59724 _59725).
Proof. exact (@lem4813749 (term185 _110859 s t _59724) (term185 _110859 t s _59725) (R _59724 _59725)). Qed.
Lemma lem4817591 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term465 _110859 t s R _59724 _59725) = (term466 _110859 t s R _59724 _59725).
Proof. exact (@lem4813749 (term79 _110859 t _59725) (s _59725) (R _59724 _59725)). Qed.
Lemma lem4817592 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (_59724 : _110859) : (term188 _110859 s t _59724) = (term188 _110859 s t _59724).
Proof. exact (eq_refl (term188 _110859 s t _59724)). Qed.
Lemma lem4817593 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term464 _110859 t s R _59724 _59725) = (term467 _110859 t s R _59724 _59725).
Proof. exact (MK_COMB (@lem4817592 _110859 s t _59724) (@lem4817591 _110859 t s R _59724 _59725)). Qed.
Lemma lem4817600 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term467 _110859 t s R _59724 _59725) = (term468 _110859 t s R _59724 _59725).
Proof. exact (@lem4813749 (term79 _110859 s _59724) (t _59724) (term466 _110859 t s R _59724 _59725)). Qed.
Lemma lem4817601 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term464 _110859 t s R _59724 _59725) = (term468 _110859 t s R _59724 _59725).
Proof. exact (TRANS (@lem4817593 _110859 t s R _59724 _59725) (@lem4817600 _110859 t s R _59724 _59725)). Qed.
Lemma lem4817603 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term452 _110859 t s R _59724 _59725) = (term468 _110859 t s R _59724 _59725).
Proof. exact (TRANS (@lem4817584 _110859 t s R _59724 _59725) (@lem4817601 _110859 t s R _59724 _59725)). Qed.
Lemma lem4817604 {_110859 : Type'} (_59724 : _110859) (_59725 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term468 _110859 t s R _59724 _59725.
Proof. exact (EQ_MP (@lem4817603 _110859 t s R _59724 _59725) (@lem4817026 _110859 _59724 _59725 x y t s R h1)). Qed.
Lemma lem4817650 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term164 _110859 t R _59728 _59729) = (term453 _110859 t R _59728 _59729).
Proof. exact (@lem4813749 (term79 _110859 t _59728) (term154 _110859 t _59728 _59729) (R _59728 _59729)). Qed.
Lemma lem4817657 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term454 _110859 t R _59728 _59729) = (term455 _110859 t R _59728 _59729).
Proof. exact (@lem4813749 (term79 _110859 t _59729) (_59728 = _59729) (R _59728 _59729)). Qed.
Lemma lem4817658 {_110859 : Type'} (t : _110859 -> Prop) (_59728 : _110859) : (term152 _110859 t _59728) = (term152 _110859 t _59728).
Proof. exact (eq_refl (term152 _110859 t _59728)). Qed.
Lemma lem4817661 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term453 _110859 t R _59728 _59729) = (term456 _110859 t R _59728 _59729).
Proof. exact (MK_COMB (@lem4817658 _110859 t _59728) (@lem4817657 _110859 t R _59728 _59729)). Qed.
Lemma lem4817663 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term164 _110859 t R _59728 _59729) = (term456 _110859 t R _59728 _59729).
Proof. exact (TRANS (@lem4817650 _110859 t R _59728 _59729) (@lem4817661 _110859 t R _59728 _59729)). Qed.
Lemma lem4817664 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term456 _110859 t R _59728 _59729.
Proof. exact (EQ_MP (@lem4817663 _110859 t R _59728 _59729) (@lem4816990 _110859 _59728 _59729 x y t s R h1)). Qed.
Lemma lem4817668 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term41 _110859 x y.
Proof. exact (proj2 (@lem4816043 _110859 x y t s R h1)). Qed.
Lemma lem4817670 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (h1). Qed.
Lemma lem4817672 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4817767 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : s x.
Proof. exact (proj1 (@lem4816012 _110859 s R x y h1)). Qed.
Lemma lem4817768 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term469 _110859 s x.
Proof. exact (fun h0 : term79 _110859 s x => @lem4817767 _110859 s R x y h1). Qed.
Lemma lem4817770 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4817771 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term469 _110859 s x) = (s x).
Proof. exact (@lem4817770 (s x)). Qed.
Lemma lem4817772 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : s x.
Proof. exact (EQ_MP (@lem4817771 _110859 s x) (@lem4817768 _110859 s R x y h1)). Qed.
Lemma lem4817774 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : s y.
Proof. exact (proj1 (@lem4816013 _110859 s R x y h1)). Qed.
Lemma lem4817775 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term469 _110859 s y.
Proof. exact (fun h0 : term79 _110859 s y => @lem4817774 _110859 s R x y h1). Qed.
Lemma lem4817777 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4817778 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term469 _110859 s y) = (s y).
Proof. exact (@lem4817777 (s y)). Qed.
Lemma lem4817779 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : s y.
Proof. exact (EQ_MP (@lem4817778 _110859 s y) (@lem4817775 _110859 s R x y h1)). Qed.
Lemma lem4817781 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816009 _110859 s R x y h1)). Qed.
Lemma lem4817782 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4817781 _110859 s R x y h1). Qed.
Lemma lem4817784 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4817785 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4817784 (R x y)). Qed.
Lemma lem4817786 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4817785 _110859 R x y) (@lem4817782 _110859 s R x y h1)). Qed.
Lemma lem4817802 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4817803 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term455 _110859 s R _59700 _59701) = (term473 _110859 s R _59700 _59701).
Proof. exact (@lem4817802 (_59700 = _59701) (term79 _110859 s _59701) (R _59700 _59701)). Qed.
Lemma lem4817819 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4817820 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term474 _110859 s R _59700 _59701) = (term475 _110859 R _59700 s _59701).
Proof. exact (@lem4817819 (R _59700 _59701) (term79 _110859 s _59701)). Qed.
Lemma lem4817826 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) : (term476 _110859 _59700 _59701) = (term476 _110859 _59700 _59701).
Proof. exact (eq_refl (term476 _110859 _59700 _59701)). Qed.
Lemma lem4817827 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term473 _110859 s R _59700 _59701) = (term477 _110859 R _59700 s _59701).
Proof. exact (MK_COMB (@lem4817826 _110859 _59700 _59701) (@lem4817820 _110859 R _59700 s _59701)). Qed.
Lemma lem4817831 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4817832 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term477 _110859 R _59700 s _59701) = (term478 _110859 R _59700 s _59701).
Proof. exact (@lem4817831 (R _59700 _59701) (_59700 = _59701) (term79 _110859 s _59701)). Qed.
Lemma lem4817850 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term473 _110859 s R _59700 _59701) = (term478 _110859 R _59700 s _59701).
Proof. exact (TRANS (@lem4817827 _110859 R _59700 s _59701) (@lem4817832 _110859 R _59700 s _59701)). Qed.
Lemma lem4817851 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term455 _110859 s R _59700 _59701) = (term478 _110859 R _59700 s _59701).
Proof. exact (TRANS (@lem4817803 _110859 s R _59700 _59701) (@lem4817850 _110859 R _59700 s _59701)). Qed.
Lemma lem4817852 {_110859 : Type'} (s : _110859 -> Prop) (_59700 : _110859) : (term152 _110859 s _59700) = (term152 _110859 s _59700).
Proof. exact (eq_refl (term152 _110859 s _59700)). Qed.
Lemma lem4817853 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term456 _110859 s R _59700 _59701) = (term479 _110859 R _59700 s _59701).
Proof. exact (MK_COMB (@lem4817852 _110859 s _59700) (@lem4817851 _110859 R _59700 s _59701)). Qed.
Lemma lem4817857 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4817858 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term479 _110859 R _59700 s _59701) = (term480 _110859 R _59700 s _59701).
Proof. exact (@lem4817857 (R _59700 _59701) (term79 _110859 s _59700) (term481 _110859 _59700 s _59701)). Qed.
Lemma lem4817872 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4817873 {_110859 : Type'} (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term482 _110859 _59700 s _59701) = (term483 _110859 _59700 s _59701).
Proof. exact (@lem4817872 (_59700 = _59701) (term79 _110859 s _59700) (term79 _110859 s _59701)). Qed.
Lemma lem4817891 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term484 _110859 R _59700 _59701) = (term484 _110859 R _59700 _59701).
Proof. exact (eq_refl (term484 _110859 R _59700 _59701)). Qed.
Lemma lem4817892 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term480 _110859 R _59700 s _59701) = (term485 _110859 R _59700 s _59701).
Proof. exact (MK_COMB (@lem4817891 _110859 R _59700 _59701) (@lem4817873 _110859 _59700 s _59701)). Qed.
Lemma lem4817903 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term479 _110859 R _59700 s _59701) = (term485 _110859 R _59700 s _59701).
Proof. exact (TRANS (@lem4817858 _110859 R _59700 s _59701) (@lem4817892 _110859 R _59700 s _59701)). Qed.
Lemma lem4817904 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term456 _110859 s R _59700 _59701) = (term485 _110859 R _59700 s _59701).
Proof. exact (TRANS (@lem4817853 _110859 R _59700 s _59701) (@lem4817903 _110859 R _59700 s _59701)). Qed.
Lemma lem4817905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4817906 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term486 _110859 s R _59700 _59701) = (term487 _110859 R _59700 s _59701).
Proof. exact (MK_COMB (@lem4817905) (@lem4817904 _110859 R _59700 s _59701)). Qed.
Lemma lem4817932 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4817933 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term474 _110859 s R _59700 _59701) = (term475 _110859 R _59700 s _59701).
Proof. exact (@lem4817932 (R _59700 _59701) (term79 _110859 s _59701)). Qed.
Lemma lem4817939 {_110859 : Type'} (s : _110859 -> Prop) (_59700 : _110859) : (term152 _110859 s _59700) = (term152 _110859 s _59700).
Proof. exact (eq_refl (term152 _110859 s _59700)). Qed.
Lemma lem4817940 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term488 _110859 s R _59700 _59701) = (term489 _110859 R _59700 s _59701).
Proof. exact (MK_COMB (@lem4817939 _110859 s _59700) (@lem4817933 _110859 R _59700 s _59701)). Qed.
Lemma lem4817944 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4817945 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term489 _110859 R _59700 s _59701) = (term490 _110859 R _59700 s _59701).
Proof. exact (@lem4817944 (R _59700 _59701) (term79 _110859 s _59700) (term79 _110859 s _59701)). Qed.
Lemma lem4817961 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term488 _110859 s R _59700 _59701) = (term490 _110859 R _59700 s _59701).
Proof. exact (TRANS (@lem4817940 _110859 R _59700 s _59701) (@lem4817945 _110859 R _59700 s _59701)). Qed.
Lemma lem4817962 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) : (term476 _110859 _59700 _59701) = (term476 _110859 _59700 _59701).
Proof. exact (eq_refl (term476 _110859 _59700 _59701)). Qed.
Lemma lem4817963 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term491 _110859 s R _59700 _59701) = (term492 _110859 R _59700 s _59701).
Proof. exact (MK_COMB (@lem4817962 _110859 _59700 _59701) (@lem4817961 _110859 R _59700 s _59701)). Qed.
Lemma lem4817967 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4817968 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term492 _110859 R _59700 s _59701) = (term485 _110859 R _59700 s _59701).
Proof. exact (@lem4817967 (R _59700 _59701) (_59700 = _59701) (term493 _110859 _59700 s _59701)). Qed.
Lemma lem4817996 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : (term491 _110859 s R _59700 _59701) = (term485 _110859 R _59700 s _59701).
Proof. exact (TRANS (@lem4817963 _110859 R _59700 s _59701) (@lem4817968 _110859 R _59700 s _59701)). Qed.
Lemma lem4817997 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : ((term456 _110859 s R _59700 _59701) = (term491 _110859 s R _59700 _59701)) = ((term485 _110859 R _59700 s _59701) = (term485 _110859 R _59700 s _59701)).
Proof. exact (MK_COMB (@lem4817906 _110859 R _59700 s _59701) (@lem4817996 _110859 R _59700 s _59701)). Qed.
Lemma lem4817999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4818000 (x : Prop) : (x = x) = True.
Proof. exact (@lem4817999 Prop x). Qed.
Lemma lem4818001 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (s : _110859 -> Prop) (_59701 : _110859) : ((term485 _110859 R _59700 s _59701) = (term485 _110859 R _59700 s _59701)) = True.
Proof. exact (@lem4818000 (term485 _110859 R _59700 s _59701)). Qed.
Lemma lem4818002 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : ((term456 _110859 s R _59700 _59701) = (term491 _110859 s R _59700 _59701)) = True.
Proof. exact (TRANS (@lem4817997 _110859 R _59700 s _59701) (@lem4818001 _110859 R _59700 s _59701)). Qed.
Lemma lem4818003 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : True = ((term456 _110859 s R _59700 _59701) = (term491 _110859 s R _59700 _59701)).
Proof. exact (SYM (@lem4818002 _110859 s R _59700 _59701)). Qed.
Lemma lem4818004 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term456 _110859 s R _59700 _59701) = (term491 _110859 s R _59700 _59701).
Proof. exact (EQ_MP (@lem4818003 _110859 s R _59700 _59701) (@lem0)). Qed.
Lemma lem4818005 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term491 _110859 s R _59700 _59701.
Proof. exact (EQ_MP (@lem4818004 _110859 s R _59700 _59701) (@lem4817090 _110859 _59700 _59701 t s R y x h1)). Qed.
Lemma lem4818007 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4818008 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term491 _110859 s R _59700 _59701) = (term495 _110859 s R _59700 _59701).
Proof. exact (@lem4818007 (term488 _110859 s R _59700 _59701) (_59700 = _59701)). Qed.
Lemma lem4818010 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818011 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term498 _110859 s R _59700 _59701) = (term499 _110859 s R _59700 _59701).
Proof. exact (@lem4818010 (term79 _110859 s _59700) (term474 _110859 s R _59700 _59701)). Qed.
Lemma lem4818013 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818014 {_110859 : Type'} (s : _110859 -> Prop) (_59700 : _110859) : (term183 _110859 s _59700) = (s _59700).
Proof. exact (@lem4818013 (s _59700)). Qed.
Lemma lem4818015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4818016 {_110859 : Type'} (s : _110859 -> Prop) (_59700 : _110859) : (term500 _110859 s _59700) = (term59 _110859 s _59700).
Proof. exact (MK_COMB (@lem4818015) (@lem4818014 _110859 s _59700)). Qed.
Lemma lem4818018 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818019 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term501 _110859 s R _59700 _59701) = (term502 _110859 s R _59700 _59701).
Proof. exact (@lem4818018 (term79 _110859 s _59701) (R _59700 _59701)). Qed.
Lemma lem4818021 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818022 {_110859 : Type'} (s : _110859 -> Prop) (_59701 : _110859) : (term183 _110859 s _59701) = (s _59701).
Proof. exact (@lem4818021 (s _59701)). Qed.
Lemma lem4818023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4818024 {_110859 : Type'} (s : _110859 -> Prop) (_59701 : _110859) : (term500 _110859 s _59701) = (term59 _110859 s _59701).
Proof. exact (MK_COMB (@lem4818023) (@lem4818022 _110859 s _59701)). Qed.
Lemma lem4818025 {_110859 : Type'} (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term438 _110859 R _59700 _59701) = (term438 _110859 R _59700 _59701).
Proof. exact (eq_refl (term438 _110859 R _59700 _59701)). Qed.
Lemma lem4818026 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term502 _110859 s R _59700 _59701) = (term503 _110859 s R _59700 _59701).
Proof. exact (MK_COMB (@lem4818024 _110859 s _59701) (@lem4818025 _110859 R _59700 _59701)). Qed.
Lemma lem4818027 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term501 _110859 s R _59700 _59701) = (term503 _110859 s R _59700 _59701).
Proof. exact (TRANS (@lem4818019 _110859 s R _59700 _59701) (@lem4818026 _110859 s R _59700 _59701)). Qed.
Lemma lem4818028 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term499 _110859 s R _59700 _59701) = (term504 _110859 s R _59700 _59701).
Proof. exact (MK_COMB (@lem4818016 _110859 s _59700) (@lem4818027 _110859 s R _59700 _59701)). Qed.
Lemma lem4818029 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term498 _110859 s R _59700 _59701) = (term504 _110859 s R _59700 _59701).
Proof. exact (TRANS (@lem4818011 _110859 s R _59700 _59701) (@lem4818028 _110859 s R _59700 _59701)). Qed.
Lemma lem4818030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4818031 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term505 _110859 s R _59700 _59701) = (term506 _110859 s R _59700 _59701).
Proof. exact (MK_COMB (@lem4818030) (@lem4818029 _110859 s R _59700 _59701)). Qed.
Lemma lem4818032 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) : (_59700 = _59701) = (_59700 = _59701).
Proof. exact (eq_refl (_59700 = _59701)). Qed.
Lemma lem4818033 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term495 _110859 s R _59700 _59701) = (term507 _110859 s R _59700 _59701).
Proof. exact (MK_COMB (@lem4818031 _110859 s R _59700 _59701) (@lem4818032 _110859 _59700 _59701)). Qed.
Lemma lem4818034 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59700 : _110859) (_59701 : _110859) : (term491 _110859 s R _59700 _59701) = (term507 _110859 s R _59700 _59701).
Proof. exact (TRANS (@lem4818008 _110859 s R _59700 _59701) (@lem4818033 _110859 s R _59700 _59701)). Qed.
Lemma lem4818036 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term503 _110859 s R x y.
Proof. exact (conj (@lem4817779 _110859 s R x y h1) (@lem4817786 _110859 s R x y h1)). Qed.
Lemma lem4818037 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term504 _110859 s R x y.
Proof. exact (conj (@lem4817772 _110859 s R x y h1) (@lem4818036 _110859 s R x y h1)). Qed.
Lemma lem4818039 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term507 _110859 s R _59700 _59701.
Proof. exact (EQ_MP (@lem4818034 _110859 s R _59700 _59701) (@lem4818005 _110859 _59700 _59701 t s R y x h1)). Qed.
Lemma lem4818040 {_110859 : Type'} (_59700 : _110859) (_59701 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term507 _110859 s R _59700 _59701.
Proof. exact (@lem4818039 _110859 _59700 _59701 t s R y x h1). Qed.
Lemma lem4818041 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term507 _110859 s R x y.
Proof. exact (@lem4818040 _110859 x y t s R y x h1). Qed.
Lemma lem4818044 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 s R x y) : x = y.
Proof. exact (@lem4818041 _110859 t s R y x h1 (@lem4818037 _110859 s R x y h2)). Qed.
Lemma lem4818045 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 s R x y) : term508 _110859 x y.
Proof. exact (fun h0 : term41 _110859 x y => @lem4818044 _110859 t s R x y h1 h2). Qed.
Lemma lem4818047 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818048 {_110859 : Type'} (x : _110859) (y : _110859) : (term508 _110859 x y) = (x = y).
Proof. exact (@lem4818047 (x = y)). Qed.
Lemma lem4818049 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 s R x y) : x = y.
Proof. exact (EQ_MP (@lem4818048 _110859 x y) (@lem4818045 _110859 t s R x y h1 h2)). Qed.
Lemma lem4818052 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4818054 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term509 _110859 x y).
Proof. exact (@lem4818052 (x = y)). Qed.
Lemma lem4818057 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 s R x y) : term509 _110859 x y.
Proof. exact (EQ_MP (@lem4818054 _110859 x y) (@lem4817036 _110859 s R x y h1)). Qed.
Lemma lem4818060 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 s R x y) : False.
Proof. exact (@lem4818057 _110859 s R x y h2 (@lem4818049 _110859 t s R x y h1 h2)). Qed.
Lemma lem4818061 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 s R x y) : term510.
Proof. exact (fun h0 : ~ False => @lem4818060 _110859 t s R x y h1 h2). Qed.
Lemma lem4818063 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818064 : term510 = False.
Proof. exact (@lem4818063 False). Qed.
Lemma lem4818065 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 s R x y) : False.
Proof. exact (EQ_MP (@lem4818064) (@lem4818061 _110859 t s R x y h1 h2)). Qed.
Lemma lem4818112 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : t x.
Proof. exact (proj1 (@lem4816020 _110859 t R x y h1)). Qed.
Lemma lem4818113 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term469 _110859 t x.
Proof. exact (fun h0 : term79 _110859 t x => @lem4818112 _110859 t R x y h1). Qed.
Lemma lem4818115 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818116 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term469 _110859 t x) = (t x).
Proof. exact (@lem4818115 (t x)). Qed.
Lemma lem4818117 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : t x.
Proof. exact (EQ_MP (@lem4818116 _110859 t x) (@lem4818113 _110859 t R x y h1)). Qed.
Lemma lem4818119 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : t y.
Proof. exact (proj1 (@lem4816021 _110859 t R x y h1)). Qed.
Lemma lem4818120 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4818119 _110859 t R x y h1). Qed.
Lemma lem4818122 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818123 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4818122 (t y)). Qed.
Lemma lem4818124 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : t y.
Proof. exact (EQ_MP (@lem4818123 _110859 t y) (@lem4818120 _110859 t R x y h1)). Qed.
Lemma lem4818126 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816017 _110859 t R x y h1)). Qed.
Lemma lem4818127 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4818126 _110859 t R x y h1). Qed.
Lemma lem4818129 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4818130 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4818129 (R x y)). Qed.
Lemma lem4818131 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4818130 _110859 R x y) (@lem4818127 _110859 t R x y h1)). Qed.
Lemma lem4818147 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818148 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term455 _110859 t R _59702 _59703) = (term473 _110859 t R _59702 _59703).
Proof. exact (@lem4818147 (_59702 = _59703) (term79 _110859 t _59703) (R _59702 _59703)). Qed.
Lemma lem4818164 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4818165 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term474 _110859 t R _59702 _59703) = (term475 _110859 R _59702 t _59703).
Proof. exact (@lem4818164 (R _59702 _59703) (term79 _110859 t _59703)). Qed.
Lemma lem4818171 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) : (term476 _110859 _59702 _59703) = (term476 _110859 _59702 _59703).
Proof. exact (eq_refl (term476 _110859 _59702 _59703)). Qed.
Lemma lem4818172 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term473 _110859 t R _59702 _59703) = (term477 _110859 R _59702 t _59703).
Proof. exact (MK_COMB (@lem4818171 _110859 _59702 _59703) (@lem4818165 _110859 R _59702 t _59703)). Qed.
Lemma lem4818176 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818177 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term477 _110859 R _59702 t _59703) = (term478 _110859 R _59702 t _59703).
Proof. exact (@lem4818176 (R _59702 _59703) (_59702 = _59703) (term79 _110859 t _59703)). Qed.
Lemma lem4818195 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term473 _110859 t R _59702 _59703) = (term478 _110859 R _59702 t _59703).
Proof. exact (TRANS (@lem4818172 _110859 R _59702 t _59703) (@lem4818177 _110859 R _59702 t _59703)). Qed.
Lemma lem4818196 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term455 _110859 t R _59702 _59703) = (term478 _110859 R _59702 t _59703).
Proof. exact (TRANS (@lem4818148 _110859 t R _59702 _59703) (@lem4818195 _110859 R _59702 t _59703)). Qed.
Lemma lem4818197 {_110859 : Type'} (t : _110859 -> Prop) (_59702 : _110859) : (term152 _110859 t _59702) = (term152 _110859 t _59702).
Proof. exact (eq_refl (term152 _110859 t _59702)). Qed.
Lemma lem4818198 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term456 _110859 t R _59702 _59703) = (term479 _110859 R _59702 t _59703).
Proof. exact (MK_COMB (@lem4818197 _110859 t _59702) (@lem4818196 _110859 R _59702 t _59703)). Qed.
Lemma lem4818202 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818203 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term479 _110859 R _59702 t _59703) = (term480 _110859 R _59702 t _59703).
Proof. exact (@lem4818202 (R _59702 _59703) (term79 _110859 t _59702) (term481 _110859 _59702 t _59703)). Qed.
Lemma lem4818217 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818218 {_110859 : Type'} (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term482 _110859 _59702 t _59703) = (term483 _110859 _59702 t _59703).
Proof. exact (@lem4818217 (_59702 = _59703) (term79 _110859 t _59702) (term79 _110859 t _59703)). Qed.
Lemma lem4818236 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term484 _110859 R _59702 _59703) = (term484 _110859 R _59702 _59703).
Proof. exact (eq_refl (term484 _110859 R _59702 _59703)). Qed.
Lemma lem4818237 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term480 _110859 R _59702 t _59703) = (term485 _110859 R _59702 t _59703).
Proof. exact (MK_COMB (@lem4818236 _110859 R _59702 _59703) (@lem4818218 _110859 _59702 t _59703)). Qed.
Lemma lem4818248 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term479 _110859 R _59702 t _59703) = (term485 _110859 R _59702 t _59703).
Proof. exact (TRANS (@lem4818203 _110859 R _59702 t _59703) (@lem4818237 _110859 R _59702 t _59703)). Qed.
Lemma lem4818249 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term456 _110859 t R _59702 _59703) = (term485 _110859 R _59702 t _59703).
Proof. exact (TRANS (@lem4818198 _110859 R _59702 t _59703) (@lem4818248 _110859 R _59702 t _59703)). Qed.
Lemma lem4818250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4818251 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term486 _110859 t R _59702 _59703) = (term487 _110859 R _59702 t _59703).
Proof. exact (MK_COMB (@lem4818250) (@lem4818249 _110859 R _59702 t _59703)). Qed.
Lemma lem4818277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4818278 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term474 _110859 t R _59702 _59703) = (term475 _110859 R _59702 t _59703).
Proof. exact (@lem4818277 (R _59702 _59703) (term79 _110859 t _59703)). Qed.
Lemma lem4818284 {_110859 : Type'} (t : _110859 -> Prop) (_59702 : _110859) : (term152 _110859 t _59702) = (term152 _110859 t _59702).
Proof. exact (eq_refl (term152 _110859 t _59702)). Qed.
Lemma lem4818285 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term488 _110859 t R _59702 _59703) = (term489 _110859 R _59702 t _59703).
Proof. exact (MK_COMB (@lem4818284 _110859 t _59702) (@lem4818278 _110859 R _59702 t _59703)). Qed.
Lemma lem4818289 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818290 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term489 _110859 R _59702 t _59703) = (term490 _110859 R _59702 t _59703).
Proof. exact (@lem4818289 (R _59702 _59703) (term79 _110859 t _59702) (term79 _110859 t _59703)). Qed.
Lemma lem4818306 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term488 _110859 t R _59702 _59703) = (term490 _110859 R _59702 t _59703).
Proof. exact (TRANS (@lem4818285 _110859 R _59702 t _59703) (@lem4818290 _110859 R _59702 t _59703)). Qed.
Lemma lem4818307 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) : (term476 _110859 _59702 _59703) = (term476 _110859 _59702 _59703).
Proof. exact (eq_refl (term476 _110859 _59702 _59703)). Qed.
Lemma lem4818308 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term491 _110859 t R _59702 _59703) = (term492 _110859 R _59702 t _59703).
Proof. exact (MK_COMB (@lem4818307 _110859 _59702 _59703) (@lem4818306 _110859 R _59702 t _59703)). Qed.
Lemma lem4818312 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818313 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term492 _110859 R _59702 t _59703) = (term485 _110859 R _59702 t _59703).
Proof. exact (@lem4818312 (R _59702 _59703) (_59702 = _59703) (term493 _110859 _59702 t _59703)). Qed.
Lemma lem4818341 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : (term491 _110859 t R _59702 _59703) = (term485 _110859 R _59702 t _59703).
Proof. exact (TRANS (@lem4818308 _110859 R _59702 t _59703) (@lem4818313 _110859 R _59702 t _59703)). Qed.
Lemma lem4818342 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : ((term456 _110859 t R _59702 _59703) = (term491 _110859 t R _59702 _59703)) = ((term485 _110859 R _59702 t _59703) = (term485 _110859 R _59702 t _59703)).
Proof. exact (MK_COMB (@lem4818251 _110859 R _59702 t _59703) (@lem4818341 _110859 R _59702 t _59703)). Qed.
Lemma lem4818344 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4818345 (x : Prop) : (x = x) = True.
Proof. exact (@lem4818344 Prop x). Qed.
Lemma lem4818346 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (t : _110859 -> Prop) (_59703 : _110859) : ((term485 _110859 R _59702 t _59703) = (term485 _110859 R _59702 t _59703)) = True.
Proof. exact (@lem4818345 (term485 _110859 R _59702 t _59703)). Qed.
Lemma lem4818347 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : ((term456 _110859 t R _59702 _59703) = (term491 _110859 t R _59702 _59703)) = True.
Proof. exact (TRANS (@lem4818342 _110859 R _59702 t _59703) (@lem4818346 _110859 R _59702 t _59703)). Qed.
Lemma lem4818348 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : True = ((term456 _110859 t R _59702 _59703) = (term491 _110859 t R _59702 _59703)).
Proof. exact (SYM (@lem4818347 _110859 t R _59702 _59703)). Qed.
Lemma lem4818349 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term456 _110859 t R _59702 _59703) = (term491 _110859 t R _59702 _59703).
Proof. exact (EQ_MP (@lem4818348 _110859 t R _59702 _59703) (@lem0)). Qed.
Lemma lem4818350 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term491 _110859 t R _59702 _59703.
Proof. exact (EQ_MP (@lem4818349 _110859 t R _59702 _59703) (@lem4817152 _110859 _59702 _59703 t s R y x h1)). Qed.
Lemma lem4818352 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4818353 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term491 _110859 t R _59702 _59703) = (term495 _110859 t R _59702 _59703).
Proof. exact (@lem4818352 (term488 _110859 t R _59702 _59703) (_59702 = _59703)). Qed.
Lemma lem4818355 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818356 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term498 _110859 t R _59702 _59703) = (term499 _110859 t R _59702 _59703).
Proof. exact (@lem4818355 (term79 _110859 t _59702) (term474 _110859 t R _59702 _59703)). Qed.
Lemma lem4818358 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818359 {_110859 : Type'} (t : _110859 -> Prop) (_59702 : _110859) : (term183 _110859 t _59702) = (t _59702).
Proof. exact (@lem4818358 (t _59702)). Qed.
Lemma lem4818360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4818361 {_110859 : Type'} (t : _110859 -> Prop) (_59702 : _110859) : (term500 _110859 t _59702) = (term59 _110859 t _59702).
Proof. exact (MK_COMB (@lem4818360) (@lem4818359 _110859 t _59702)). Qed.
Lemma lem4818363 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818364 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term501 _110859 t R _59702 _59703) = (term502 _110859 t R _59702 _59703).
Proof. exact (@lem4818363 (term79 _110859 t _59703) (R _59702 _59703)). Qed.
Lemma lem4818366 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818367 {_110859 : Type'} (t : _110859 -> Prop) (_59703 : _110859) : (term183 _110859 t _59703) = (t _59703).
Proof. exact (@lem4818366 (t _59703)). Qed.
Lemma lem4818368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4818369 {_110859 : Type'} (t : _110859 -> Prop) (_59703 : _110859) : (term500 _110859 t _59703) = (term59 _110859 t _59703).
Proof. exact (MK_COMB (@lem4818368) (@lem4818367 _110859 t _59703)). Qed.
Lemma lem4818370 {_110859 : Type'} (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term438 _110859 R _59702 _59703) = (term438 _110859 R _59702 _59703).
Proof. exact (eq_refl (term438 _110859 R _59702 _59703)). Qed.
Lemma lem4818371 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term502 _110859 t R _59702 _59703) = (term503 _110859 t R _59702 _59703).
Proof. exact (MK_COMB (@lem4818369 _110859 t _59703) (@lem4818370 _110859 R _59702 _59703)). Qed.
Lemma lem4818372 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term501 _110859 t R _59702 _59703) = (term503 _110859 t R _59702 _59703).
Proof. exact (TRANS (@lem4818364 _110859 t R _59702 _59703) (@lem4818371 _110859 t R _59702 _59703)). Qed.
Lemma lem4818373 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term499 _110859 t R _59702 _59703) = (term504 _110859 t R _59702 _59703).
Proof. exact (MK_COMB (@lem4818361 _110859 t _59702) (@lem4818372 _110859 t R _59702 _59703)). Qed.
Lemma lem4818374 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term498 _110859 t R _59702 _59703) = (term504 _110859 t R _59702 _59703).
Proof. exact (TRANS (@lem4818356 _110859 t R _59702 _59703) (@lem4818373 _110859 t R _59702 _59703)). Qed.
Lemma lem4818375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4818376 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term505 _110859 t R _59702 _59703) = (term506 _110859 t R _59702 _59703).
Proof. exact (MK_COMB (@lem4818375) (@lem4818374 _110859 t R _59702 _59703)). Qed.
Lemma lem4818377 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) : (_59702 = _59703) = (_59702 = _59703).
Proof. exact (eq_refl (_59702 = _59703)). Qed.
Lemma lem4818378 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term495 _110859 t R _59702 _59703) = (term507 _110859 t R _59702 _59703).
Proof. exact (MK_COMB (@lem4818376 _110859 t R _59702 _59703) (@lem4818377 _110859 _59702 _59703)). Qed.
Lemma lem4818379 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59702 : _110859) (_59703 : _110859) : (term491 _110859 t R _59702 _59703) = (term507 _110859 t R _59702 _59703).
Proof. exact (TRANS (@lem4818353 _110859 t R _59702 _59703) (@lem4818378 _110859 t R _59702 _59703)). Qed.
Lemma lem4818381 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term503 _110859 t R x y.
Proof. exact (conj (@lem4818124 _110859 t R x y h1) (@lem4818131 _110859 t R x y h1)). Qed.
Lemma lem4818382 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term504 _110859 t R x y.
Proof. exact (conj (@lem4818117 _110859 t R x y h1) (@lem4818381 _110859 t R x y h1)). Qed.
Lemma lem4818384 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term507 _110859 t R _59702 _59703.
Proof. exact (EQ_MP (@lem4818379 _110859 t R _59702 _59703) (@lem4818350 _110859 _59702 _59703 t s R y x h1)). Qed.
Lemma lem4818385 {_110859 : Type'} (_59702 : _110859) (_59703 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term507 _110859 t R _59702 _59703.
Proof. exact (@lem4818384 _110859 _59702 _59703 t s R y x h1). Qed.
Lemma lem4818386 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term507 _110859 t R x y.
Proof. exact (@lem4818385 _110859 x y t s R y x h1). Qed.
Lemma lem4818389 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 t R x y) : x = y.
Proof. exact (@lem4818386 _110859 t s R y x h1 (@lem4818382 _110859 t R x y h2)). Qed.
Lemma lem4818390 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 t R x y) : term508 _110859 x y.
Proof. exact (fun h0 : term41 _110859 x y => @lem4818389 _110859 s t R x y h1 h2). Qed.
Lemma lem4818392 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818393 {_110859 : Type'} (x : _110859) (y : _110859) : (term508 _110859 x y) = (x = y).
Proof. exact (@lem4818392 (x = y)). Qed.
Lemma lem4818394 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 t R x y) : x = y.
Proof. exact (EQ_MP (@lem4818393 _110859 x y) (@lem4818390 _110859 s t R x y h1 h2)). Qed.
Lemma lem4818397 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4818399 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term509 _110859 x y).
Proof. exact (@lem4818397 (x = y)). Qed.
Lemma lem4818402 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term160 _110859 t R x y) : term509 _110859 x y.
Proof. exact (EQ_MP (@lem4818399 _110859 x y) (@lem4817116 _110859 t R x y h1)). Qed.
Lemma lem4818405 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 t R x y) : False.
Proof. exact (@lem4818402 _110859 t R x y h2 (@lem4818394 _110859 s t R x y h1 h2)). Qed.
Lemma lem4818406 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 t R x y) : term510.
Proof. exact (fun h0 : ~ False => @lem4818405 _110859 s t R x y h1 h2). Qed.
Lemma lem4818408 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818409 : term510 = False.
Proof. exact (@lem4818408 False). Qed.
Lemma lem4818410 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term333 _110859 t s R y x) (h2 : term160 _110859 t R x y) : False.
Proof. exact (EQ_MP (@lem4818409) (@lem4818406 _110859 s t R x y h1 h2)). Qed.
Lemma lem4818430 {_110859 : Type'} (s : _110859 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4818431 {_110859 : Type'} (_59752 : _110859) (_59753 : _110859) (h1 : _59752 = _59753) : _59752 = _59753.
Proof. exact (h1). Qed.
Lemma lem4818432 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) (_59753 : _110859) (h1 : _59752 = _59753) : (s _59752) = (s _59753).
Proof. exact (MK_COMB (@lem4818430 _110859 s) (@lem4818431 _110859 _59752 _59753 h1)). Qed.
Lemma lem4818434 (b : Prop) (a : Prop) : term511 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4818435 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : term512 _110859 _59753 s _59752.
Proof. exact (@lem4818434 (s _59753) (s _59752)). Qed.
Lemma lem4818436 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) (_59753 : _110859) (h1 : _59752 = _59753) : term513 _110859 _59753 s _59752.
Proof. exact (@lem4818435 _110859 _59753 s _59752 (@lem4818432 _110859 s _59752 _59753 h1)). Qed.
Lemma lem4818437 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : term514 _110859 _59753 s _59752.
Proof. exact (fun h0 : _59752 = _59753 => @lem4818436 _110859 s _59752 _59753 h0). Qed.
Lemma lem4818439 (a : Prop) (b : Prop) : (a -> b) = (term515 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4818440 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : (term514 _110859 _59753 s _59752) = (term516 _110859 _59753 s _59752).
Proof. exact (@lem4818439 (_59752 = _59753) (term513 _110859 _59753 s _59752)). Qed.
Lemma lem4818441 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : term516 _110859 _59753 s _59752.
Proof. exact (EQ_MP (@lem4818440 _110859 _59753 s _59752) (@lem4818437 _110859 _59753 s _59752)). Qed.
Lemma lem4818457 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : s x.
Proof. exact (proj1 (@lem4816028 _110859 t s R y x h1)). Qed.
Lemma lem4818458 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term469 _110859 s x.
Proof. exact (fun h0 : term79 _110859 s x => @lem4818457 _110859 t s R y x h1). Qed.
Lemma lem4818460 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818461 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term469 _110859 s x) = (s x).
Proof. exact (@lem4818460 (s x)). Qed.
Lemma lem4818462 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : s x.
Proof. exact (EQ_MP (@lem4818461 _110859 s x) (@lem4818458 _110859 t s R y x h1)). Qed.
Lemma lem4818464 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : t y.
Proof. exact (proj1 (@lem4816027 _110859 t s R y x h1)). Qed.
Lemma lem4818465 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4818464 _110859 t s R y x h1). Qed.
Lemma lem4818467 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818468 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4818467 (t y)). Qed.
Lemma lem4818469 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : t y.
Proof. exact (EQ_MP (@lem4818468 _110859 t y) (@lem4818465 _110859 t s R y x h1)). Qed.
Lemma lem4818471 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term79 _110859 s y.
Proof. exact (proj2 (@lem4816027 _110859 t s R y x h1)). Qed.
Lemma lem4818472 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term517 _110859 s y.
Proof. exact (fun h0 : s y => @lem4818471 _110859 t s R y x h1). Qed.
Lemma lem4818474 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4818475 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term517 _110859 s y) = (term79 _110859 s y).
Proof. exact (@lem4818474 (s y)). Qed.
Lemma lem4818476 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term79 _110859 s y.
Proof. exact (EQ_MP (@lem4818475 _110859 s y) (@lem4818472 _110859 t s R y x h1)). Qed.
Lemma lem4818478 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : s x.
Proof. exact (proj1 (@lem4816028 _110859 t s R y x h1)). Qed.
Lemma lem4818479 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term469 _110859 s x.
Proof. exact (fun h0 : term79 _110859 s x => @lem4818478 _110859 t s R y x h1). Qed.
Lemma lem4818481 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818482 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term469 _110859 s x) = (s x).
Proof. exact (@lem4818481 (s x)). Qed.
Lemma lem4818483 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : s x.
Proof. exact (EQ_MP (@lem4818482 _110859 s x) (@lem4818479 _110859 t s R y x h1)). Qed.
Lemma lem4818485 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4818486 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) (_59753 : _110859) : (term516 _110859 _59753 s _59752) = (term518 _110859 s _59752 _59753).
Proof. exact (@lem4818485 (term513 _110859 _59753 s _59752) (term41 _110859 _59752 _59753)). Qed.
Lemma lem4818488 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818489 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : (term519 _110859 _59753 s _59752) = (term520 _110859 _59753 s _59752).
Proof. exact (@lem4818488 (s _59753) (term79 _110859 s _59752)). Qed.
Lemma lem4818491 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818492 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) : (term183 _110859 s _59752) = (s _59752).
Proof. exact (@lem4818491 (s _59752)). Qed.
Lemma lem4818493 {_110859 : Type'} (s : _110859 -> Prop) (_59753 : _110859) : (term521 _110859 s _59753) = (term521 _110859 s _59753).
Proof. exact (eq_refl (term521 _110859 s _59753)). Qed.
Lemma lem4818494 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : (term520 _110859 _59753 s _59752) = (term522 _110859 _59753 s _59752).
Proof. exact (MK_COMB (@lem4818493 _110859 s _59753) (@lem4818492 _110859 s _59752)). Qed.
Lemma lem4818495 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : (term519 _110859 _59753 s _59752) = (term522 _110859 _59753 s _59752).
Proof. exact (TRANS (@lem4818489 _110859 _59753 s _59752) (@lem4818494 _110859 _59753 s _59752)). Qed.
Lemma lem4818496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4818497 {_110859 : Type'} (_59753 : _110859) (s : _110859 -> Prop) (_59752 : _110859) : (term523 _110859 _59753 s _59752) = (term524 _110859 _59753 s _59752).
Proof. exact (MK_COMB (@lem4818496) (@lem4818495 _110859 _59753 s _59752)). Qed.
Lemma lem4818498 {_110859 : Type'} (_59752 : _110859) (_59753 : _110859) : (term41 _110859 _59752 _59753) = (term41 _110859 _59752 _59753).
Proof. exact (eq_refl (term41 _110859 _59752 _59753)). Qed.
Lemma lem4818499 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) (_59753 : _110859) : (term518 _110859 s _59752 _59753) = (term525 _110859 s _59752 _59753).
Proof. exact (MK_COMB (@lem4818497 _110859 _59753 s _59752) (@lem4818498 _110859 _59752 _59753)). Qed.
Lemma lem4818500 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) (_59753 : _110859) : (term516 _110859 _59753 s _59752) = (term525 _110859 s _59752 _59753).
Proof. exact (TRANS (@lem4818486 _110859 s _59752 _59753) (@lem4818499 _110859 s _59752 _59753)). Qed.
Lemma lem4818502 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term522 _110859 y s x.
Proof. exact (conj (@lem4818476 _110859 t s R y x h1) (@lem4818483 _110859 t s R y x h1)). Qed.
Lemma lem4818504 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) (_59753 : _110859) : term525 _110859 s _59752 _59753.
Proof. exact (EQ_MP (@lem4818500 _110859 s _59752 _59753) (@lem4818441 _110859 _59753 s _59752)). Qed.
Lemma lem4818505 {_110859 : Type'} (s : _110859 -> Prop) (_59752 : _110859) (_59753 : _110859) : term525 _110859 s _59752 _59753.
Proof. exact (@lem4818504 _110859 s _59752 _59753). Qed.
Lemma lem4818506 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (y : _110859) : term525 _110859 s x y.
Proof. exact (@lem4818505 _110859 s x y). Qed.
Lemma lem4818509 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term41 _110859 x y.
Proof. exact (@lem4818506 _110859 s x y (@lem4818502 _110859 t s R y x h1)). Qed.
Lemma lem4818510 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term526 _110859 x y.
Proof. exact (fun h0 : x = y => @lem4818509 _110859 t s R y x h1). Qed.
Lemma lem4818512 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4818513 {_110859 : Type'} (x : _110859) (y : _110859) : (term526 _110859 x y) = (term41 _110859 x y).
Proof. exact (@lem4818512 (x = y)). Qed.
Lemma lem4818514 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term41 _110859 x y.
Proof. exact (EQ_MP (@lem4818513 _110859 x y) (@lem4818510 _110859 t s R y x h1)). Qed.
Lemma lem4818530 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818531 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term455 _110859 t R _59704 _59705) = (term473 _110859 t R _59704 _59705).
Proof. exact (@lem4818530 (_59704 = _59705) (term79 _110859 t _59705) (R _59704 _59705)). Qed.
Lemma lem4818547 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4818548 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term474 _110859 t R _59704 _59705) = (term475 _110859 R _59704 t _59705).
Proof. exact (@lem4818547 (R _59704 _59705) (term79 _110859 t _59705)). Qed.
Lemma lem4818554 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) : (term476 _110859 _59704 _59705) = (term476 _110859 _59704 _59705).
Proof. exact (eq_refl (term476 _110859 _59704 _59705)). Qed.
Lemma lem4818555 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term473 _110859 t R _59704 _59705) = (term477 _110859 R _59704 t _59705).
Proof. exact (MK_COMB (@lem4818554 _110859 _59704 _59705) (@lem4818548 _110859 R _59704 t _59705)). Qed.
Lemma lem4818559 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818560 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term477 _110859 R _59704 t _59705) = (term478 _110859 R _59704 t _59705).
Proof. exact (@lem4818559 (R _59704 _59705) (_59704 = _59705) (term79 _110859 t _59705)). Qed.
Lemma lem4818578 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term473 _110859 t R _59704 _59705) = (term478 _110859 R _59704 t _59705).
Proof. exact (TRANS (@lem4818555 _110859 R _59704 t _59705) (@lem4818560 _110859 R _59704 t _59705)). Qed.
Lemma lem4818579 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term455 _110859 t R _59704 _59705) = (term478 _110859 R _59704 t _59705).
Proof. exact (TRANS (@lem4818531 _110859 t R _59704 _59705) (@lem4818578 _110859 R _59704 t _59705)). Qed.
Lemma lem4818580 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) : (term152 _110859 s _59704) = (term152 _110859 s _59704).
Proof. exact (eq_refl (term152 _110859 s _59704)). Qed.
Lemma lem4818581 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term458 _110859 s t R _59704 _59705) = (term527 _110859 s R _59704 t _59705).
Proof. exact (MK_COMB (@lem4818580 _110859 s _59704) (@lem4818579 _110859 R _59704 t _59705)). Qed.
Lemma lem4818585 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818586 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term527 _110859 s R _59704 t _59705) = (term528 _110859 R s _59704 t _59705).
Proof. exact (@lem4818585 (R _59704 _59705) (term79 _110859 s _59704) (term481 _110859 _59704 t _59705)). Qed.
Lemma lem4818600 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818601 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term529 _110859 s _59704 t _59705) = (term530 _110859 s _59704 t _59705).
Proof. exact (@lem4818600 (_59704 = _59705) (term79 _110859 s _59704) (term79 _110859 t _59705)). Qed.
Lemma lem4818619 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term484 _110859 R _59704 _59705) = (term484 _110859 R _59704 _59705).
Proof. exact (eq_refl (term484 _110859 R _59704 _59705)). Qed.
Lemma lem4818620 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term528 _110859 R s _59704 t _59705) = (term531 _110859 R s _59704 t _59705).
Proof. exact (MK_COMB (@lem4818619 _110859 R _59704 _59705) (@lem4818601 _110859 s _59704 t _59705)). Qed.
Lemma lem4818631 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term527 _110859 s R _59704 t _59705) = (term531 _110859 R s _59704 t _59705).
Proof. exact (TRANS (@lem4818586 _110859 R s _59704 t _59705) (@lem4818620 _110859 R s _59704 t _59705)). Qed.
Lemma lem4818632 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term458 _110859 s t R _59704 _59705) = (term531 _110859 R s _59704 t _59705).
Proof. exact (TRANS (@lem4818581 _110859 s R _59704 t _59705) (@lem4818631 _110859 R s _59704 t _59705)). Qed.
Lemma lem4818633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4818634 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term532 _110859 s t R _59704 _59705) = (term533 _110859 R s _59704 t _59705).
Proof. exact (MK_COMB (@lem4818633) (@lem4818632 _110859 R s _59704 t _59705)). Qed.
Lemma lem4818658 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4818659 {_110859 : Type'} (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term154 _110859 t _59704 _59705) = (term481 _110859 _59704 t _59705).
Proof. exact (@lem4818658 (_59704 = _59705) (term79 _110859 t _59705)). Qed.
Lemma lem4818667 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) : (term152 _110859 s _59704) = (term152 _110859 s _59704).
Proof. exact (eq_refl (term152 _110859 s _59704)). Qed.
Lemma lem4818668 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term428 _110859 s t _59704 _59705) = (term529 _110859 s _59704 t _59705).
Proof. exact (MK_COMB (@lem4818667 _110859 s _59704) (@lem4818659 _110859 _59704 t _59705)). Qed.
Lemma lem4818672 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818673 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term529 _110859 s _59704 t _59705) = (term530 _110859 s _59704 t _59705).
Proof. exact (@lem4818672 (_59704 = _59705) (term79 _110859 s _59704) (term79 _110859 t _59705)). Qed.
Lemma lem4818691 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term428 _110859 s t _59704 _59705) = (term530 _110859 s _59704 t _59705).
Proof. exact (TRANS (@lem4818668 _110859 s _59704 t _59705) (@lem4818673 _110859 s _59704 t _59705)). Qed.
Lemma lem4818692 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term484 _110859 R _59704 _59705) = (term484 _110859 R _59704 _59705).
Proof. exact (eq_refl (term484 _110859 R _59704 _59705)). Qed.
Lemma lem4818693 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : (term534 _110859 R s t _59704 _59705) = (term531 _110859 R s _59704 t _59705).
Proof. exact (MK_COMB (@lem4818692 _110859 R _59704 _59705) (@lem4818691 _110859 s _59704 t _59705)). Qed.
Lemma lem4818704 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : ((term458 _110859 s t R _59704 _59705) = (term534 _110859 R s t _59704 _59705)) = ((term531 _110859 R s _59704 t _59705) = (term531 _110859 R s _59704 t _59705)).
Proof. exact (MK_COMB (@lem4818634 _110859 R s _59704 t _59705) (@lem4818693 _110859 R s _59704 t _59705)). Qed.
Lemma lem4818706 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4818707 (x : Prop) : (x = x) = True.
Proof. exact (@lem4818706 Prop x). Qed.
Lemma lem4818708 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59704 : _110859) (t : _110859 -> Prop) (_59705 : _110859) : ((term531 _110859 R s _59704 t _59705) = (term531 _110859 R s _59704 t _59705)) = True.
Proof. exact (@lem4818707 (term531 _110859 R s _59704 t _59705)). Qed.
Lemma lem4818709 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : ((term458 _110859 s t R _59704 _59705) = (term534 _110859 R s t _59704 _59705)) = True.
Proof. exact (TRANS (@lem4818704 _110859 R s _59704 t _59705) (@lem4818708 _110859 R s _59704 t _59705)). Qed.
Lemma lem4818710 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : True = ((term458 _110859 s t R _59704 _59705) = (term534 _110859 R s t _59704 _59705)).
Proof. exact (SYM (@lem4818709 _110859 R s t _59704 _59705)). Qed.
Lemma lem4818711 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term458 _110859 s t R _59704 _59705) = (term534 _110859 R s t _59704 _59705).
Proof. exact (EQ_MP (@lem4818710 _110859 R s t _59704 _59705) (@lem0)). Qed.
Lemma lem4818712 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term534 _110859 R s t _59704 _59705.
Proof. exact (EQ_MP (@lem4818711 _110859 R s t _59704 _59705) (@lem4817216 _110859 _59704 _59705 t s R y x h1)). Qed.
Lemma lem4818714 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4818715 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term534 _110859 R s t _59704 _59705) = (term535 _110859 s t R _59704 _59705).
Proof. exact (@lem4818714 (term428 _110859 s t _59704 _59705) (R _59704 _59705)). Qed.
Lemma lem4818717 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818718 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term536 _110859 s t _59704 _59705) = (term537 _110859 s t _59704 _59705).
Proof. exact (@lem4818717 (term79 _110859 s _59704) (term154 _110859 t _59704 _59705)). Qed.
Lemma lem4818720 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818721 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) : (term183 _110859 s _59704) = (s _59704).
Proof. exact (@lem4818720 (s _59704)). Qed.
Lemma lem4818722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4818723 {_110859 : Type'} (s : _110859 -> Prop) (_59704 : _110859) : (term500 _110859 s _59704) = (term59 _110859 s _59704).
Proof. exact (MK_COMB (@lem4818722) (@lem4818721 _110859 s _59704)). Qed.
Lemma lem4818725 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818726 {_110859 : Type'} (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term538 _110859 t _59704 _59705) = (term539 _110859 t _59704 _59705).
Proof. exact (@lem4818725 (term79 _110859 t _59705) (_59704 = _59705)). Qed.
Lemma lem4818728 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818729 {_110859 : Type'} (t : _110859 -> Prop) (_59705 : _110859) : (term183 _110859 t _59705) = (t _59705).
Proof. exact (@lem4818728 (t _59705)). Qed.
Lemma lem4818730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4818731 {_110859 : Type'} (t : _110859 -> Prop) (_59705 : _110859) : (term500 _110859 t _59705) = (term59 _110859 t _59705).
Proof. exact (MK_COMB (@lem4818730) (@lem4818729 _110859 t _59705)). Qed.
Lemma lem4818732 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) : (term41 _110859 _59704 _59705) = (term41 _110859 _59704 _59705).
Proof. exact (eq_refl (term41 _110859 _59704 _59705)). Qed.
Lemma lem4818733 {_110859 : Type'} (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term539 _110859 t _59704 _59705) = (term61 _110859 t _59704 _59705).
Proof. exact (MK_COMB (@lem4818731 _110859 t _59705) (@lem4818732 _110859 _59704 _59705)). Qed.
Lemma lem4818734 {_110859 : Type'} (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term538 _110859 t _59704 _59705) = (term61 _110859 t _59704 _59705).
Proof. exact (TRANS (@lem4818726 _110859 t _59704 _59705) (@lem4818733 _110859 t _59704 _59705)). Qed.
Lemma lem4818735 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term537 _110859 s t _59704 _59705) = (term540 _110859 s t _59704 _59705).
Proof. exact (MK_COMB (@lem4818723 _110859 s _59704) (@lem4818734 _110859 t _59704 _59705)). Qed.
Lemma lem4818736 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term536 _110859 s t _59704 _59705) = (term540 _110859 s t _59704 _59705).
Proof. exact (TRANS (@lem4818718 _110859 s t _59704 _59705) (@lem4818735 _110859 s t _59704 _59705)). Qed.
Lemma lem4818737 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4818738 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (_59704 : _110859) (_59705 : _110859) : (term541 _110859 s t _59704 _59705) = (term542 _110859 s t _59704 _59705).
Proof. exact (MK_COMB (@lem4818737) (@lem4818736 _110859 s t _59704 _59705)). Qed.
Lemma lem4818739 {_110859 : Type'} (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (R _59704 _59705) = (R _59704 _59705).
Proof. exact (eq_refl (R _59704 _59705)). Qed.
Lemma lem4818740 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term535 _110859 s t R _59704 _59705) = (term543 _110859 s t R _59704 _59705).
Proof. exact (MK_COMB (@lem4818738 _110859 s t _59704 _59705) (@lem4818739 _110859 R _59704 _59705)). Qed.
Lemma lem4818741 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59704 : _110859) (_59705 : _110859) : (term534 _110859 R s t _59704 _59705) = (term543 _110859 s t R _59704 _59705).
Proof. exact (TRANS (@lem4818715 _110859 s t R _59704 _59705) (@lem4818740 _110859 s t R _59704 _59705)). Qed.
Lemma lem4818743 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term61 _110859 t x y.
Proof. exact (conj (@lem4818469 _110859 t s R y x h1) (@lem4818514 _110859 t s R y x h1)). Qed.
Lemma lem4818744 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term540 _110859 s t x y.
Proof. exact (conj (@lem4818462 _110859 t s R y x h1) (@lem4818743 _110859 t s R y x h1)). Qed.
Lemma lem4818746 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term543 _110859 s t R _59704 _59705.
Proof. exact (EQ_MP (@lem4818741 _110859 s t R _59704 _59705) (@lem4818712 _110859 _59704 _59705 t s R y x h1)). Qed.
Lemma lem4818747 {_110859 : Type'} (_59704 : _110859) (_59705 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term543 _110859 s t R _59704 _59705.
Proof. exact (@lem4818746 _110859 _59704 _59705 t s R y x h1). Qed.
Lemma lem4818748 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term543 _110859 s t R x y.
Proof. exact (@lem4818747 _110859 x y t s R y x h1). Qed.
Lemma lem4818751 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term196 _110859 t s R y x) : R x y.
Proof. exact (@lem4818748 _110859 t s R y x h1 (@lem4818744 _110859 t s R y x h2)). Qed.
Lemma lem4818752 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term196 _110859 t s R y x) : term544 _110859 R x y.
Proof. exact (fun h0 : term438 _110859 R x y => @lem4818751 _110859 t s R y x h1 h2). Qed.
Lemma lem4818754 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818755 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term544 _110859 R x y) = (R x y).
Proof. exact (@lem4818754 (R x y)). Qed.
Lemma lem4818756 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term196 _110859 t s R y x) : R x y.
Proof. exact (EQ_MP (@lem4818755 _110859 R x y) (@lem4818752 _110859 t s R y x h1 h2)). Qed.
Lemma lem4818759 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4818761 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term438 _110859 R x y) = (term545 _110859 R x y).
Proof. exact (@lem4818759 (R x y)). Qed.
Lemma lem4818764 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) (h1 : term438 _110859 R x y) : term545 _110859 R x y.
Proof. exact (EQ_MP (@lem4818761 _110859 R x y) (@lem4817198 _110859 R x y h1)). Qed.
Lemma lem4818767 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (@lem4818764 _110859 R x y h1 (@lem4818756 _110859 t s R y x h2 h3)). Qed.
Lemma lem4818768 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : term510.
Proof. exact (fun h0 : ~ False => @lem4818767 _110859 t s R y x h1 h2 h3). Qed.
Lemma lem4818770 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818771 : term510 = False.
Proof. exact (@lem4818770 False). Qed.
Lemma lem4818772 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4818771) (@lem4818768 _110859 t s R y x h1 h2 h3)). Qed.
Lemma lem4818804 {_110859 : Type'} (t : _110859 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4818805 {_110859 : Type'} (_59762 : _110859) (_59763 : _110859) (h1 : _59762 = _59763) : _59762 = _59763.
Proof. exact (h1). Qed.
Lemma lem4818806 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) (_59763 : _110859) (h1 : _59762 = _59763) : (t _59762) = (t _59763).
Proof. exact (MK_COMB (@lem4818804 _110859 t) (@lem4818805 _110859 _59762 _59763 h1)). Qed.
Lemma lem4818808 (b : Prop) (a : Prop) : term511 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4818809 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : term512 _110859 _59763 t _59762.
Proof. exact (@lem4818808 (t _59763) (t _59762)). Qed.
Lemma lem4818810 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) (_59763 : _110859) (h1 : _59762 = _59763) : term513 _110859 _59763 t _59762.
Proof. exact (@lem4818809 _110859 _59763 t _59762 (@lem4818806 _110859 t _59762 _59763 h1)). Qed.
Lemma lem4818811 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : term514 _110859 _59763 t _59762.
Proof. exact (fun h0 : _59762 = _59763 => @lem4818810 _110859 t _59762 _59763 h0). Qed.
Lemma lem4818813 (a : Prop) (b : Prop) : (a -> b) = (term515 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4818814 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : (term514 _110859 _59763 t _59762) = (term516 _110859 _59763 t _59762).
Proof. exact (@lem4818813 (_59762 = _59763) (term513 _110859 _59763 t _59762)). Qed.
Lemma lem4818815 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : term516 _110859 _59763 t _59762.
Proof. exact (EQ_MP (@lem4818814 _110859 _59763 t _59762) (@lem4818811 _110859 _59763 t _59762)). Qed.
Lemma lem4818819 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : t y.
Proof. exact (proj1 (@lem4816027 _110859 t s R y x h1)). Qed.
Lemma lem4818820 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4818819 _110859 t s R y x h1). Qed.
Lemma lem4818822 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818823 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4818822 (t y)). Qed.
Lemma lem4818824 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : t y.
Proof. exact (EQ_MP (@lem4818823 _110859 t y) (@lem4818820 _110859 t s R y x h1)). Qed.
Lemma lem4818826 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : s x.
Proof. exact (proj1 (@lem4816028 _110859 t s R y x h1)). Qed.
Lemma lem4818827 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term469 _110859 s x.
Proof. exact (fun h0 : term79 _110859 s x => @lem4818826 _110859 t s R y x h1). Qed.
Lemma lem4818829 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818830 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term469 _110859 s x) = (s x).
Proof. exact (@lem4818829 (s x)). Qed.
Lemma lem4818831 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : s x.
Proof. exact (EQ_MP (@lem4818830 _110859 s x) (@lem4818827 _110859 t s R y x h1)). Qed.
Lemma lem4818833 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term79 _110859 t x.
Proof. exact (proj2 (@lem4816028 _110859 t s R y x h1)). Qed.
Lemma lem4818834 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term517 _110859 t x.
Proof. exact (fun h0 : t x => @lem4818833 _110859 t s R y x h1). Qed.
Lemma lem4818836 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4818837 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term517 _110859 t x) = (term79 _110859 t x).
Proof. exact (@lem4818836 (t x)). Qed.
Lemma lem4818838 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term79 _110859 t x.
Proof. exact (EQ_MP (@lem4818837 _110859 t x) (@lem4818834 _110859 t s R y x h1)). Qed.
Lemma lem4818840 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : t y.
Proof. exact (proj1 (@lem4816027 _110859 t s R y x h1)). Qed.
Lemma lem4818841 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4818840 _110859 t s R y x h1). Qed.
Lemma lem4818843 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4818844 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4818843 (t y)). Qed.
Lemma lem4818845 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : t y.
Proof. exact (EQ_MP (@lem4818844 _110859 t y) (@lem4818841 _110859 t s R y x h1)). Qed.
Lemma lem4818847 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4818848 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) (_59763 : _110859) : (term516 _110859 _59763 t _59762) = (term518 _110859 t _59762 _59763).
Proof. exact (@lem4818847 (term513 _110859 _59763 t _59762) (term41 _110859 _59762 _59763)). Qed.
Lemma lem4818850 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4818851 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : (term519 _110859 _59763 t _59762) = (term520 _110859 _59763 t _59762).
Proof. exact (@lem4818850 (t _59763) (term79 _110859 t _59762)). Qed.
Lemma lem4818853 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4818854 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) : (term183 _110859 t _59762) = (t _59762).
Proof. exact (@lem4818853 (t _59762)). Qed.
Lemma lem4818855 {_110859 : Type'} (t : _110859 -> Prop) (_59763 : _110859) : (term521 _110859 t _59763) = (term521 _110859 t _59763).
Proof. exact (eq_refl (term521 _110859 t _59763)). Qed.
Lemma lem4818856 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : (term520 _110859 _59763 t _59762) = (term522 _110859 _59763 t _59762).
Proof. exact (MK_COMB (@lem4818855 _110859 t _59763) (@lem4818854 _110859 t _59762)). Qed.
Lemma lem4818857 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : (term519 _110859 _59763 t _59762) = (term522 _110859 _59763 t _59762).
Proof. exact (TRANS (@lem4818851 _110859 _59763 t _59762) (@lem4818856 _110859 _59763 t _59762)). Qed.
Lemma lem4818858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4818859 {_110859 : Type'} (_59763 : _110859) (t : _110859 -> Prop) (_59762 : _110859) : (term523 _110859 _59763 t _59762) = (term524 _110859 _59763 t _59762).
Proof. exact (MK_COMB (@lem4818858) (@lem4818857 _110859 _59763 t _59762)). Qed.
Lemma lem4818860 {_110859 : Type'} (_59762 : _110859) (_59763 : _110859) : (term41 _110859 _59762 _59763) = (term41 _110859 _59762 _59763).
Proof. exact (eq_refl (term41 _110859 _59762 _59763)). Qed.
Lemma lem4818861 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) (_59763 : _110859) : (term518 _110859 t _59762 _59763) = (term525 _110859 t _59762 _59763).
Proof. exact (MK_COMB (@lem4818859 _110859 _59763 t _59762) (@lem4818860 _110859 _59762 _59763)). Qed.
Lemma lem4818862 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) (_59763 : _110859) : (term516 _110859 _59763 t _59762) = (term525 _110859 t _59762 _59763).
Proof. exact (TRANS (@lem4818848 _110859 t _59762 _59763) (@lem4818861 _110859 t _59762 _59763)). Qed.
Lemma lem4818864 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term522 _110859 x t y.
Proof. exact (conj (@lem4818838 _110859 t s R y x h1) (@lem4818845 _110859 t s R y x h1)). Qed.
Lemma lem4818866 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) (_59763 : _110859) : term525 _110859 t _59762 _59763.
Proof. exact (EQ_MP (@lem4818862 _110859 t _59762 _59763) (@lem4818815 _110859 _59763 t _59762)). Qed.
Lemma lem4818867 {_110859 : Type'} (t : _110859 -> Prop) (_59762 : _110859) (_59763 : _110859) : term525 _110859 t _59762 _59763.
Proof. exact (@lem4818866 _110859 t _59762 _59763). Qed.
Lemma lem4818868 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (x : _110859) : term525 _110859 t y x.
Proof. exact (@lem4818867 _110859 t y x). Qed.
Lemma lem4818871 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term41 _110859 y x.
Proof. exact (@lem4818868 _110859 t y x (@lem4818864 _110859 t s R y x h1)). Qed.
Lemma lem4818872 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term526 _110859 y x.
Proof. exact (fun h0 : y = x => @lem4818871 _110859 t s R y x h1). Qed.
Lemma lem4818874 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4818875 {_110859 : Type'} (y : _110859) (x : _110859) : (term526 _110859 y x) = (term41 _110859 y x).
Proof. exact (@lem4818874 (y = x)). Qed.
Lemma lem4818876 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term41 _110859 y x.
Proof. exact (EQ_MP (@lem4818875 _110859 y x) (@lem4818872 _110859 t s R y x h1)). Qed.
Lemma lem4818882 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818883 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term458 _110859 t s R _59706 _59707) = (term546 _110859 s t R _59706 _59707).
Proof. exact (@lem4818882 (term79 _110859 s _59707) (term79 _110859 t _59706) (term547 _110859 R _59706 _59707)). Qed.
Lemma lem4818897 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818898 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term548 _110859 t R _59706 _59707) = (term549 _110859 t R _59706 _59707).
Proof. exact (@lem4818897 (_59706 = _59707) (term79 _110859 t _59706) (R _59706 _59707)). Qed.
Lemma lem4818914 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4818915 {_110859 : Type'} (R : type1402 _110859) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term550 _110859 t R _59706 _59707) = (term551 _110859 R _59707 t _59706).
Proof. exact (@lem4818914 (R _59706 _59707) (term79 _110859 t _59706)). Qed.
Lemma lem4818921 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) : (term476 _110859 _59706 _59707) = (term476 _110859 _59706 _59707).
Proof. exact (eq_refl (term476 _110859 _59706 _59707)). Qed.
Lemma lem4818922 {_110859 : Type'} (R : type1402 _110859) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term549 _110859 t R _59706 _59707) = (term552 _110859 R _59707 t _59706).
Proof. exact (MK_COMB (@lem4818921 _110859 _59706 _59707) (@lem4818915 _110859 R _59707 t _59706)). Qed.
Lemma lem4818926 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818927 {_110859 : Type'} (R : type1402 _110859) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term552 _110859 R _59707 t _59706) = (term553 _110859 R _59707 t _59706).
Proof. exact (@lem4818926 (R _59706 _59707) (_59706 = _59707) (term79 _110859 t _59706)). Qed.
Lemma lem4818945 {_110859 : Type'} (R : type1402 _110859) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term549 _110859 t R _59706 _59707) = (term553 _110859 R _59707 t _59706).
Proof. exact (TRANS (@lem4818922 _110859 R _59707 t _59706) (@lem4818927 _110859 R _59707 t _59706)). Qed.
Lemma lem4818946 {_110859 : Type'} (R : type1402 _110859) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term548 _110859 t R _59706 _59707) = (term553 _110859 R _59707 t _59706).
Proof. exact (TRANS (@lem4818898 _110859 t R _59706 _59707) (@lem4818945 _110859 R _59707 t _59706)). Qed.
Lemma lem4818947 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) : (term152 _110859 s _59707) = (term152 _110859 s _59707).
Proof. exact (eq_refl (term152 _110859 s _59707)). Qed.
Lemma lem4818948 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term546 _110859 s t R _59706 _59707) = (term554 _110859 s R _59707 t _59706).
Proof. exact (MK_COMB (@lem4818947 _110859 s _59707) (@lem4818946 _110859 R _59707 t _59706)). Qed.
Lemma lem4818952 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818953 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term554 _110859 s R _59707 t _59706) = (term555 _110859 R s _59707 t _59706).
Proof. exact (@lem4818952 (R _59706 _59707) (term79 _110859 s _59707) (term556 _110859 _59707 t _59706)). Qed.
Lemma lem4818967 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4818968 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term557 _110859 s _59707 t _59706) = (term558 _110859 s _59707 t _59706).
Proof. exact (@lem4818967 (_59706 = _59707) (term79 _110859 s _59707) (term79 _110859 t _59706)). Qed.
Lemma lem4818986 {_110859 : Type'} (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term484 _110859 R _59706 _59707) = (term484 _110859 R _59706 _59707).
Proof. exact (eq_refl (term484 _110859 R _59706 _59707)). Qed.
Lemma lem4818987 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term555 _110859 R s _59707 t _59706) = (term559 _110859 R s _59707 t _59706).
Proof. exact (MK_COMB (@lem4818986 _110859 R _59706 _59707) (@lem4818968 _110859 s _59707 t _59706)). Qed.
Lemma lem4818998 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term554 _110859 s R _59707 t _59706) = (term559 _110859 R s _59707 t _59706).
Proof. exact (TRANS (@lem4818953 _110859 R s _59707 t _59706) (@lem4818987 _110859 R s _59707 t _59706)). Qed.
Lemma lem4818999 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term546 _110859 s t R _59706 _59707) = (term559 _110859 R s _59707 t _59706).
Proof. exact (TRANS (@lem4818948 _110859 s R _59707 t _59706) (@lem4818998 _110859 R s _59707 t _59706)). Qed.
Lemma lem4819000 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term458 _110859 t s R _59706 _59707) = (term559 _110859 R s _59707 t _59706).
Proof. exact (TRANS (@lem4818883 _110859 s t R _59706 _59707) (@lem4818999 _110859 R s _59707 t _59706)). Qed.
Lemma lem4819001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4819002 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term532 _110859 t s R _59706 _59707) = (term560 _110859 R s _59707 t _59706).
Proof. exact (MK_COMB (@lem4819001) (@lem4819000 _110859 R s _59707 t _59706)). Qed.
Lemma lem4819016 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819017 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term428 _110859 t s _59706 _59707) = (term561 _110859 s t _59706 _59707).
Proof. exact (@lem4819016 (term79 _110859 s _59707) (term79 _110859 t _59706) (_59706 = _59707)). Qed.
Lemma lem4819031 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4819032 {_110859 : Type'} (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term562 _110859 t _59706 _59707) = (term556 _110859 _59707 t _59706).
Proof. exact (@lem4819031 (_59706 = _59707) (term79 _110859 t _59706)). Qed.
Lemma lem4819040 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) : (term152 _110859 s _59707) = (term152 _110859 s _59707).
Proof. exact (eq_refl (term152 _110859 s _59707)). Qed.
Lemma lem4819041 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term561 _110859 s t _59706 _59707) = (term557 _110859 s _59707 t _59706).
Proof. exact (MK_COMB (@lem4819040 _110859 s _59707) (@lem4819032 _110859 _59707 t _59706)). Qed.
Lemma lem4819045 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819046 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term557 _110859 s _59707 t _59706) = (term558 _110859 s _59707 t _59706).
Proof. exact (@lem4819045 (_59706 = _59707) (term79 _110859 s _59707) (term79 _110859 t _59706)). Qed.
Lemma lem4819064 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term561 _110859 s t _59706 _59707) = (term558 _110859 s _59707 t _59706).
Proof. exact (TRANS (@lem4819041 _110859 s _59707 t _59706) (@lem4819046 _110859 s _59707 t _59706)). Qed.
Lemma lem4819065 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term428 _110859 t s _59706 _59707) = (term558 _110859 s _59707 t _59706).
Proof. exact (TRANS (@lem4819017 _110859 s t _59706 _59707) (@lem4819064 _110859 s _59707 t _59706)). Qed.
Lemma lem4819066 {_110859 : Type'} (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term484 _110859 R _59706 _59707) = (term484 _110859 R _59706 _59707).
Proof. exact (eq_refl (term484 _110859 R _59706 _59707)). Qed.
Lemma lem4819067 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : (term534 _110859 R t s _59706 _59707) = (term559 _110859 R s _59707 t _59706).
Proof. exact (MK_COMB (@lem4819066 _110859 R _59706 _59707) (@lem4819065 _110859 s _59707 t _59706)). Qed.
Lemma lem4819078 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : ((term458 _110859 t s R _59706 _59707) = (term534 _110859 R t s _59706 _59707)) = ((term559 _110859 R s _59707 t _59706) = (term559 _110859 R s _59707 t _59706)).
Proof. exact (MK_COMB (@lem4819002 _110859 R s _59707 t _59706) (@lem4819067 _110859 R s _59707 t _59706)). Qed.
Lemma lem4819080 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4819081 (x : Prop) : (x = x) = True.
Proof. exact (@lem4819080 Prop x). Qed.
Lemma lem4819082 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59707 : _110859) (t : _110859 -> Prop) (_59706 : _110859) : ((term559 _110859 R s _59707 t _59706) = (term559 _110859 R s _59707 t _59706)) = True.
Proof. exact (@lem4819081 (term559 _110859 R s _59707 t _59706)). Qed.
Lemma lem4819083 {_110859 : Type'} (R : type1402 _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : ((term458 _110859 t s R _59706 _59707) = (term534 _110859 R t s _59706 _59707)) = True.
Proof. exact (TRANS (@lem4819078 _110859 R s _59707 t _59706) (@lem4819082 _110859 R s _59707 t _59706)). Qed.
Lemma lem4819084 {_110859 : Type'} (R : type1402 _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : True = ((term458 _110859 t s R _59706 _59707) = (term534 _110859 R t s _59706 _59707)).
Proof. exact (SYM (@lem4819083 _110859 R t s _59706 _59707)). Qed.
Lemma lem4819085 {_110859 : Type'} (R : type1402 _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term458 _110859 t s R _59706 _59707) = (term534 _110859 R t s _59706 _59707).
Proof. exact (EQ_MP (@lem4819084 _110859 R t s _59706 _59707) (@lem0)). Qed.
Lemma lem4819086 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term534 _110859 R t s _59706 _59707.
Proof. exact (EQ_MP (@lem4819085 _110859 R t s _59706 _59707) (@lem4817352 _110859 _59706 _59707 t s R y x h1)). Qed.
Lemma lem4819088 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4819089 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term534 _110859 R t s _59706 _59707) = (term535 _110859 t s R _59706 _59707).
Proof. exact (@lem4819088 (term428 _110859 t s _59706 _59707) (R _59706 _59707)). Qed.
Lemma lem4819091 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4819092 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term536 _110859 t s _59706 _59707) = (term537 _110859 t s _59706 _59707).
Proof. exact (@lem4819091 (term79 _110859 t _59706) (term154 _110859 s _59706 _59707)). Qed.
Lemma lem4819094 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4819095 {_110859 : Type'} (t : _110859 -> Prop) (_59706 : _110859) : (term183 _110859 t _59706) = (t _59706).
Proof. exact (@lem4819094 (t _59706)). Qed.
Lemma lem4819096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4819097 {_110859 : Type'} (t : _110859 -> Prop) (_59706 : _110859) : (term500 _110859 t _59706) = (term59 _110859 t _59706).
Proof. exact (MK_COMB (@lem4819096) (@lem4819095 _110859 t _59706)). Qed.
Lemma lem4819099 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4819100 {_110859 : Type'} (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term538 _110859 s _59706 _59707) = (term539 _110859 s _59706 _59707).
Proof. exact (@lem4819099 (term79 _110859 s _59707) (_59706 = _59707)). Qed.
Lemma lem4819102 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4819103 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) : (term183 _110859 s _59707) = (s _59707).
Proof. exact (@lem4819102 (s _59707)). Qed.
Lemma lem4819104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4819105 {_110859 : Type'} (s : _110859 -> Prop) (_59707 : _110859) : (term500 _110859 s _59707) = (term59 _110859 s _59707).
Proof. exact (MK_COMB (@lem4819104) (@lem4819103 _110859 s _59707)). Qed.
Lemma lem4819106 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) : (term41 _110859 _59706 _59707) = (term41 _110859 _59706 _59707).
Proof. exact (eq_refl (term41 _110859 _59706 _59707)). Qed.
Lemma lem4819107 {_110859 : Type'} (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term539 _110859 s _59706 _59707) = (term61 _110859 s _59706 _59707).
Proof. exact (MK_COMB (@lem4819105 _110859 s _59707) (@lem4819106 _110859 _59706 _59707)). Qed.
Lemma lem4819108 {_110859 : Type'} (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term538 _110859 s _59706 _59707) = (term61 _110859 s _59706 _59707).
Proof. exact (TRANS (@lem4819100 _110859 s _59706 _59707) (@lem4819107 _110859 s _59706 _59707)). Qed.
Lemma lem4819109 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term537 _110859 t s _59706 _59707) = (term540 _110859 t s _59706 _59707).
Proof. exact (MK_COMB (@lem4819097 _110859 t _59706) (@lem4819108 _110859 s _59706 _59707)). Qed.
Lemma lem4819110 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term536 _110859 t s _59706 _59707) = (term540 _110859 t s _59706 _59707).
Proof. exact (TRANS (@lem4819092 _110859 t s _59706 _59707) (@lem4819109 _110859 t s _59706 _59707)). Qed.
Lemma lem4819111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4819112 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (_59706 : _110859) (_59707 : _110859) : (term541 _110859 t s _59706 _59707) = (term542 _110859 t s _59706 _59707).
Proof. exact (MK_COMB (@lem4819111) (@lem4819110 _110859 t s _59706 _59707)). Qed.
Lemma lem4819113 {_110859 : Type'} (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (R _59706 _59707) = (R _59706 _59707).
Proof. exact (eq_refl (R _59706 _59707)). Qed.
Lemma lem4819114 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term535 _110859 t s R _59706 _59707) = (term543 _110859 t s R _59706 _59707).
Proof. exact (MK_COMB (@lem4819112 _110859 t s _59706 _59707) (@lem4819113 _110859 R _59706 _59707)). Qed.
Lemma lem4819115 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59706 : _110859) (_59707 : _110859) : (term534 _110859 R t s _59706 _59707) = (term543 _110859 t s R _59706 _59707).
Proof. exact (TRANS (@lem4819089 _110859 t s R _59706 _59707) (@lem4819114 _110859 t s R _59706 _59707)). Qed.
Lemma lem4819117 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term61 _110859 s y x.
Proof. exact (conj (@lem4818831 _110859 t s R y x h1) (@lem4818876 _110859 t s R y x h1)). Qed.
Lemma lem4819118 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term196 _110859 t s R y x) : term540 _110859 t s y x.
Proof. exact (conj (@lem4818824 _110859 t s R y x h1) (@lem4819117 _110859 t s R y x h1)). Qed.
Lemma lem4819120 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term543 _110859 t s R _59706 _59707.
Proof. exact (EQ_MP (@lem4819115 _110859 t s R _59706 _59707) (@lem4819086 _110859 _59706 _59707 t s R y x h1)). Qed.
Lemma lem4819121 {_110859 : Type'} (_59706 : _110859) (_59707 : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term543 _110859 t s R _59706 _59707.
Proof. exact (@lem4819120 _110859 _59706 _59707 t s R y x h1). Qed.
Lemma lem4819122 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : term543 _110859 t s R y x.
Proof. exact (@lem4819121 _110859 y x t s R y x h1). Qed.
Lemma lem4819125 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term196 _110859 t s R y x) : R y x.
Proof. exact (@lem4819122 _110859 t s R y x h1 (@lem4819118 _110859 t s R y x h2)). Qed.
Lemma lem4819126 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term196 _110859 t s R y x) : term544 _110859 R y x.
Proof. exact (fun h0 : term438 _110859 R y x => @lem4819125 _110859 t s R y x h1 h2). Qed.
Lemma lem4819128 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819129 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) : (term544 _110859 R y x) = (R y x).
Proof. exact (@lem4819128 (R y x)). Qed.
Lemma lem4819130 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term196 _110859 t s R y x) : R y x.
Proof. exact (EQ_MP (@lem4819129 _110859 R y x) (@lem4819126 _110859 t s R y x h1 h2)). Qed.
Lemma lem4819133 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4819135 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) : (term438 _110859 R y x) = (term545 _110859 R y x).
Proof. exact (@lem4819133 (R y x)). Qed.
Lemma lem4819138 {_110859 : Type'} (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) : term545 _110859 R y x.
Proof. exact (EQ_MP (@lem4819135 _110859 R y x) (@lem4817280 _110859 R y x h1)). Qed.
Lemma lem4819141 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (@lem4819138 _110859 R y x h1 (@lem4819130 _110859 t s R y x h2 h3)). Qed.
Lemma lem4819142 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : term510.
Proof. exact (fun h0 : ~ False => @lem4819141 _110859 t s R y x h1 h2 h3). Qed.
Lemma lem4819144 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819145 : term510 = False.
Proof. exact (@lem4819144 False). Qed.
Lemma lem4819146 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4819145) (@lem4819142 _110859 t s R y x h1 h2 h3)). Qed.
Lemma lem4819193 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4819194 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : term469 _110859 s x.
Proof. exact (fun h0 : term79 _110859 s x => @lem4819193 _110859 s x h1). Qed.
Lemma lem4819196 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819197 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term469 _110859 s x) = (s x).
Proof. exact (@lem4819196 (s x)). Qed.
Lemma lem4819198 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4819197 _110859 s x) (@lem4819194 _110859 s x h1)). Qed.
Lemma lem4819200 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (h1). Qed.
Lemma lem4819201 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : term469 _110859 s y.
Proof. exact (fun h0 : term79 _110859 s y => @lem4819200 _110859 s y h1). Qed.
Lemma lem4819203 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819204 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term469 _110859 s y) = (s y).
Proof. exact (@lem4819203 (s y)). Qed.
Lemma lem4819205 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (EQ_MP (@lem4819204 _110859 s y) (@lem4819201 _110859 s y h1)). Qed.
Lemma lem4819207 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4819208 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4819207 _110859 x y t s R h1). Qed.
Lemma lem4819210 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4819211 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4819210 (R x y)). Qed.
Lemma lem4819212 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4819211 _110859 R x y) (@lem4819208 _110859 x y t s R h1)). Qed.
Lemma lem4819228 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819229 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term455 _110859 s R _59708 _59709) = (term473 _110859 s R _59708 _59709).
Proof. exact (@lem4819228 (_59708 = _59709) (term79 _110859 s _59709) (R _59708 _59709)). Qed.
Lemma lem4819245 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4819246 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term474 _110859 s R _59708 _59709) = (term475 _110859 R _59708 s _59709).
Proof. exact (@lem4819245 (R _59708 _59709) (term79 _110859 s _59709)). Qed.
Lemma lem4819252 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) : (term476 _110859 _59708 _59709) = (term476 _110859 _59708 _59709).
Proof. exact (eq_refl (term476 _110859 _59708 _59709)). Qed.
Lemma lem4819253 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term473 _110859 s R _59708 _59709) = (term477 _110859 R _59708 s _59709).
Proof. exact (MK_COMB (@lem4819252 _110859 _59708 _59709) (@lem4819246 _110859 R _59708 s _59709)). Qed.
Lemma lem4819257 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819258 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term477 _110859 R _59708 s _59709) = (term478 _110859 R _59708 s _59709).
Proof. exact (@lem4819257 (R _59708 _59709) (_59708 = _59709) (term79 _110859 s _59709)). Qed.
Lemma lem4819276 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term473 _110859 s R _59708 _59709) = (term478 _110859 R _59708 s _59709).
Proof. exact (TRANS (@lem4819253 _110859 R _59708 s _59709) (@lem4819258 _110859 R _59708 s _59709)). Qed.
Lemma lem4819277 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term455 _110859 s R _59708 _59709) = (term478 _110859 R _59708 s _59709).
Proof. exact (TRANS (@lem4819229 _110859 s R _59708 _59709) (@lem4819276 _110859 R _59708 s _59709)). Qed.
Lemma lem4819278 {_110859 : Type'} (s : _110859 -> Prop) (_59708 : _110859) : (term152 _110859 s _59708) = (term152 _110859 s _59708).
Proof. exact (eq_refl (term152 _110859 s _59708)). Qed.
Lemma lem4819279 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term456 _110859 s R _59708 _59709) = (term479 _110859 R _59708 s _59709).
Proof. exact (MK_COMB (@lem4819278 _110859 s _59708) (@lem4819277 _110859 R _59708 s _59709)). Qed.
Lemma lem4819283 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819284 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term479 _110859 R _59708 s _59709) = (term480 _110859 R _59708 s _59709).
Proof. exact (@lem4819283 (R _59708 _59709) (term79 _110859 s _59708) (term481 _110859 _59708 s _59709)). Qed.
Lemma lem4819298 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819299 {_110859 : Type'} (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term482 _110859 _59708 s _59709) = (term483 _110859 _59708 s _59709).
Proof. exact (@lem4819298 (_59708 = _59709) (term79 _110859 s _59708) (term79 _110859 s _59709)). Qed.
Lemma lem4819317 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term484 _110859 R _59708 _59709) = (term484 _110859 R _59708 _59709).
Proof. exact (eq_refl (term484 _110859 R _59708 _59709)). Qed.
Lemma lem4819318 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term480 _110859 R _59708 s _59709) = (term485 _110859 R _59708 s _59709).
Proof. exact (MK_COMB (@lem4819317 _110859 R _59708 _59709) (@lem4819299 _110859 _59708 s _59709)). Qed.
Lemma lem4819329 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term479 _110859 R _59708 s _59709) = (term485 _110859 R _59708 s _59709).
Proof. exact (TRANS (@lem4819284 _110859 R _59708 s _59709) (@lem4819318 _110859 R _59708 s _59709)). Qed.
Lemma lem4819330 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term456 _110859 s R _59708 _59709) = (term485 _110859 R _59708 s _59709).
Proof. exact (TRANS (@lem4819279 _110859 R _59708 s _59709) (@lem4819329 _110859 R _59708 s _59709)). Qed.
Lemma lem4819331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4819332 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term486 _110859 s R _59708 _59709) = (term487 _110859 R _59708 s _59709).
Proof. exact (MK_COMB (@lem4819331) (@lem4819330 _110859 R _59708 s _59709)). Qed.
Lemma lem4819358 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4819359 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term474 _110859 s R _59708 _59709) = (term475 _110859 R _59708 s _59709).
Proof. exact (@lem4819358 (R _59708 _59709) (term79 _110859 s _59709)). Qed.
Lemma lem4819365 {_110859 : Type'} (s : _110859 -> Prop) (_59708 : _110859) : (term152 _110859 s _59708) = (term152 _110859 s _59708).
Proof. exact (eq_refl (term152 _110859 s _59708)). Qed.
Lemma lem4819366 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term488 _110859 s R _59708 _59709) = (term489 _110859 R _59708 s _59709).
Proof. exact (MK_COMB (@lem4819365 _110859 s _59708) (@lem4819359 _110859 R _59708 s _59709)). Qed.
Lemma lem4819370 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819371 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term489 _110859 R _59708 s _59709) = (term490 _110859 R _59708 s _59709).
Proof. exact (@lem4819370 (R _59708 _59709) (term79 _110859 s _59708) (term79 _110859 s _59709)). Qed.
Lemma lem4819387 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term488 _110859 s R _59708 _59709) = (term490 _110859 R _59708 s _59709).
Proof. exact (TRANS (@lem4819366 _110859 R _59708 s _59709) (@lem4819371 _110859 R _59708 s _59709)). Qed.
Lemma lem4819388 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) : (term476 _110859 _59708 _59709) = (term476 _110859 _59708 _59709).
Proof. exact (eq_refl (term476 _110859 _59708 _59709)). Qed.
Lemma lem4819389 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term491 _110859 s R _59708 _59709) = (term492 _110859 R _59708 s _59709).
Proof. exact (MK_COMB (@lem4819388 _110859 _59708 _59709) (@lem4819387 _110859 R _59708 s _59709)). Qed.
Lemma lem4819393 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819394 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term492 _110859 R _59708 s _59709) = (term485 _110859 R _59708 s _59709).
Proof. exact (@lem4819393 (R _59708 _59709) (_59708 = _59709) (term493 _110859 _59708 s _59709)). Qed.
Lemma lem4819422 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : (term491 _110859 s R _59708 _59709) = (term485 _110859 R _59708 s _59709).
Proof. exact (TRANS (@lem4819389 _110859 R _59708 s _59709) (@lem4819394 _110859 R _59708 s _59709)). Qed.
Lemma lem4819423 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : ((term456 _110859 s R _59708 _59709) = (term491 _110859 s R _59708 _59709)) = ((term485 _110859 R _59708 s _59709) = (term485 _110859 R _59708 s _59709)).
Proof. exact (MK_COMB (@lem4819332 _110859 R _59708 s _59709) (@lem4819422 _110859 R _59708 s _59709)). Qed.
Lemma lem4819425 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4819426 (x : Prop) : (x = x) = True.
Proof. exact (@lem4819425 Prop x). Qed.
Lemma lem4819427 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (s : _110859 -> Prop) (_59709 : _110859) : ((term485 _110859 R _59708 s _59709) = (term485 _110859 R _59708 s _59709)) = True.
Proof. exact (@lem4819426 (term485 _110859 R _59708 s _59709)). Qed.
Lemma lem4819428 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : ((term456 _110859 s R _59708 _59709) = (term491 _110859 s R _59708 _59709)) = True.
Proof. exact (TRANS (@lem4819423 _110859 R _59708 s _59709) (@lem4819427 _110859 R _59708 s _59709)). Qed.
Lemma lem4819429 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : True = ((term456 _110859 s R _59708 _59709) = (term491 _110859 s R _59708 _59709)).
Proof. exact (SYM (@lem4819428 _110859 s R _59708 _59709)). Qed.
Lemma lem4819430 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term456 _110859 s R _59708 _59709) = (term491 _110859 s R _59708 _59709).
Proof. exact (EQ_MP (@lem4819429 _110859 s R _59708 _59709) (@lem0)). Qed.
Lemma lem4819431 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term491 _110859 s R _59708 _59709.
Proof. exact (EQ_MP (@lem4819430 _110859 s R _59708 _59709) (@lem4817370 _110859 _59708 _59709 x y t s R h1)). Qed.
Lemma lem4819433 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4819434 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term491 _110859 s R _59708 _59709) = (term495 _110859 s R _59708 _59709).
Proof. exact (@lem4819433 (term488 _110859 s R _59708 _59709) (_59708 = _59709)). Qed.
Lemma lem4819436 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4819437 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term498 _110859 s R _59708 _59709) = (term499 _110859 s R _59708 _59709).
Proof. exact (@lem4819436 (term79 _110859 s _59708) (term474 _110859 s R _59708 _59709)). Qed.
Lemma lem4819439 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4819440 {_110859 : Type'} (s : _110859 -> Prop) (_59708 : _110859) : (term183 _110859 s _59708) = (s _59708).
Proof. exact (@lem4819439 (s _59708)). Qed.
Lemma lem4819441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4819442 {_110859 : Type'} (s : _110859 -> Prop) (_59708 : _110859) : (term500 _110859 s _59708) = (term59 _110859 s _59708).
Proof. exact (MK_COMB (@lem4819441) (@lem4819440 _110859 s _59708)). Qed.
Lemma lem4819444 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4819445 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term501 _110859 s R _59708 _59709) = (term502 _110859 s R _59708 _59709).
Proof. exact (@lem4819444 (term79 _110859 s _59709) (R _59708 _59709)). Qed.
Lemma lem4819447 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4819448 {_110859 : Type'} (s : _110859 -> Prop) (_59709 : _110859) : (term183 _110859 s _59709) = (s _59709).
Proof. exact (@lem4819447 (s _59709)). Qed.
Lemma lem4819449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4819450 {_110859 : Type'} (s : _110859 -> Prop) (_59709 : _110859) : (term500 _110859 s _59709) = (term59 _110859 s _59709).
Proof. exact (MK_COMB (@lem4819449) (@lem4819448 _110859 s _59709)). Qed.
Lemma lem4819451 {_110859 : Type'} (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term438 _110859 R _59708 _59709) = (term438 _110859 R _59708 _59709).
Proof. exact (eq_refl (term438 _110859 R _59708 _59709)). Qed.
Lemma lem4819452 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term502 _110859 s R _59708 _59709) = (term503 _110859 s R _59708 _59709).
Proof. exact (MK_COMB (@lem4819450 _110859 s _59709) (@lem4819451 _110859 R _59708 _59709)). Qed.
Lemma lem4819453 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term501 _110859 s R _59708 _59709) = (term503 _110859 s R _59708 _59709).
Proof. exact (TRANS (@lem4819445 _110859 s R _59708 _59709) (@lem4819452 _110859 s R _59708 _59709)). Qed.
Lemma lem4819454 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term499 _110859 s R _59708 _59709) = (term504 _110859 s R _59708 _59709).
Proof. exact (MK_COMB (@lem4819442 _110859 s _59708) (@lem4819453 _110859 s R _59708 _59709)). Qed.
Lemma lem4819455 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term498 _110859 s R _59708 _59709) = (term504 _110859 s R _59708 _59709).
Proof. exact (TRANS (@lem4819437 _110859 s R _59708 _59709) (@lem4819454 _110859 s R _59708 _59709)). Qed.
Lemma lem4819456 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4819457 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term505 _110859 s R _59708 _59709) = (term506 _110859 s R _59708 _59709).
Proof. exact (MK_COMB (@lem4819456) (@lem4819455 _110859 s R _59708 _59709)). Qed.
Lemma lem4819458 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) : (_59708 = _59709) = (_59708 = _59709).
Proof. exact (eq_refl (_59708 = _59709)). Qed.
Lemma lem4819459 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term495 _110859 s R _59708 _59709) = (term507 _110859 s R _59708 _59709).
Proof. exact (MK_COMB (@lem4819457 _110859 s R _59708 _59709) (@lem4819458 _110859 _59708 _59709)). Qed.
Lemma lem4819460 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59708 : _110859) (_59709 : _110859) : (term491 _110859 s R _59708 _59709) = (term507 _110859 s R _59708 _59709).
Proof. exact (TRANS (@lem4819434 _110859 s R _59708 _59709) (@lem4819459 _110859 s R _59708 _59709)). Qed.
Lemma lem4819462 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : term368 _110859 x y t s R) : term503 _110859 s R x y.
Proof. exact (conj (@lem4819205 _110859 s y h1) (@lem4819212 _110859 x y t s R h2)). Qed.
Lemma lem4819463 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : term504 _110859 s R x y.
Proof. exact (conj (@lem4819198 _110859 s x h1) (@lem4819462 _110859 x y t s R h2 h3)). Qed.
Lemma lem4819465 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 s R _59708 _59709.
Proof. exact (EQ_MP (@lem4819460 _110859 s R _59708 _59709) (@lem4819431 _110859 _59708 _59709 x y t s R h1)). Qed.
Lemma lem4819466 {_110859 : Type'} (_59708 : _110859) (_59709 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 s R _59708 _59709.
Proof. exact (@lem4819465 _110859 _59708 _59709 x y t s R h1). Qed.
Lemma lem4819467 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 s R x y.
Proof. exact (@lem4819466 _110859 x y x y t s R h1). Qed.
Lemma lem4819470 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : x = y.
Proof. exact (@lem4819467 _110859 x y t s R h3 (@lem4819463 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4819471 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : term508 _110859 x y.
Proof. exact (fun h0 : term41 _110859 x y => @lem4819470 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4819473 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819474 {_110859 : Type'} (x : _110859) (y : _110859) : (term508 _110859 x y) = (x = y).
Proof. exact (@lem4819473 (x = y)). Qed.
Lemma lem4819475 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : x = y.
Proof. exact (EQ_MP (@lem4819474 _110859 x y) (@lem4819471 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4819478 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4819480 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term509 _110859 x y).
Proof. exact (@lem4819478 (x = y)). Qed.
Lemma lem4819483 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term509 _110859 x y.
Proof. exact (EQ_MP (@lem4819480 _110859 x y) (@lem4817392 _110859 x y t s R h1)). Qed.
Lemma lem4819486 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (@lem4819483 _110859 x y t s R h3 (@lem4819475 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4819487 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : term510.
Proof. exact (fun h0 : ~ False => @lem4819486 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4819489 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819490 : term510 = False.
Proof. exact (@lem4819489 False). Qed.
Lemma lem4819491 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4819490) (@lem4819487 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4819538 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4819539 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : term469 _110859 t x.
Proof. exact (fun h0 : term79 _110859 t x => @lem4819538 _110859 t x h1). Qed.
Lemma lem4819541 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819542 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term469 _110859 t x) = (t x).
Proof. exact (@lem4819541 (t x)). Qed.
Lemma lem4819543 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4819542 _110859 t x) (@lem4819539 _110859 t x h1)). Qed.
Lemma lem4819545 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (h1). Qed.
Lemma lem4819546 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : term469 _110859 s y.
Proof. exact (fun h0 : term79 _110859 s y => @lem4819545 _110859 s y h1). Qed.
Lemma lem4819548 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819549 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term469 _110859 s y) = (s y).
Proof. exact (@lem4819548 (s y)). Qed.
Lemma lem4819550 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (EQ_MP (@lem4819549 _110859 s y) (@lem4819546 _110859 s y h1)). Qed.
Lemma lem4819552 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4819553 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : term469 _110859 t x.
Proof. exact (fun h0 : term79 _110859 t x => @lem4819552 _110859 t x h1). Qed.
Lemma lem4819555 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819556 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term469 _110859 t x) = (t x).
Proof. exact (@lem4819555 (t x)). Qed.
Lemma lem4819557 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4819556 _110859 t x) (@lem4819553 _110859 t x h1)). Qed.
Lemma lem4819559 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (h1). Qed.
Lemma lem4819560 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : term469 _110859 s y.
Proof. exact (fun h0 : term79 _110859 s y => @lem4819559 _110859 s y h1). Qed.
Lemma lem4819562 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4819563 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term469 _110859 s y) = (s y).
Proof. exact (@lem4819562 (s y)). Qed.
Lemma lem4819564 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) (h1 : s y) : s y.
Proof. exact (EQ_MP (@lem4819563 _110859 s y) (@lem4819560 _110859 s y h1)). Qed.
Lemma lem4819567 {_110859 : Type'} (x : _110859) (y : _110859) (h1 : term41 _110859 x y) : term41 _110859 x y.
Proof. exact (h1). Qed.
Lemma lem4819568 {_110859 : Type'} (x : _110859) (y : _110859) (h1 : term41 _110859 x y) : term526 _110859 x y.
Proof. exact (fun h0 : x = y => @lem4819567 _110859 x y h1). Qed.
Lemma lem4819570 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4819571 {_110859 : Type'} (x : _110859) (y : _110859) : (term526 _110859 x y) = (term41 _110859 x y).
Proof. exact (@lem4819570 (x = y)). Qed.
Lemma lem4819572 {_110859 : Type'} (x : _110859) (y : _110859) (h1 : term41 _110859 x y) : term41 _110859 x y.
Proof. exact (EQ_MP (@lem4819571 _110859 x y) (@lem4819568 _110859 x y h1)). Qed.
Lemma lem4819574 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4819575 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4819574 _110859 x y t s R h1). Qed.
Lemma lem4819577 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4819578 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4819577 (R x y)). Qed.
Lemma lem4819579 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4819578 _110859 R x y) (@lem4819575 _110859 x y t s R h1)). Qed.
Lemma lem4819581 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4819582 {_110859 : Type'} (R : type1402 _110859) (_59715 : _110859) (s : _110859 -> Prop) (_59714 : _110859) : (term456 _110859 s R _59714 _59715) = (term563 _110859 R _59715 s _59714).
Proof. exact (@lem4819581 (term455 _110859 s R _59714 _59715) (term79 _110859 s _59714)). Qed.
Lemma lem4819584 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4819585 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term564 _110859 s R _59714 _59715) = (term565 _110859 s R _59714 _59715).
Proof. exact (@lem4819584 (term79 _110859 s _59715) (term547 _110859 R _59714 _59715)). Qed.
Lemma lem4819587 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4819588 {_110859 : Type'} (s : _110859 -> Prop) (_59715 : _110859) : (term183 _110859 s _59715) = (s _59715).
Proof. exact (@lem4819587 (s _59715)). Qed.
Lemma lem4819589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4819590 {_110859 : Type'} (s : _110859 -> Prop) (_59715 : _110859) : (term500 _110859 s _59715) = (term59 _110859 s _59715).
Proof. exact (MK_COMB (@lem4819589) (@lem4819588 _110859 s _59715)). Qed.
Lemma lem4819592 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4819593 {_110859 : Type'} (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term566 _110859 R _59714 _59715) = (term567 _110859 R _59714 _59715).
Proof. exact (@lem4819592 (_59714 = _59715) (R _59714 _59715)). Qed.
Lemma lem4819594 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term565 _110859 s R _59714 _59715) = (term568 _110859 s R _59714 _59715).
Proof. exact (MK_COMB (@lem4819590 _110859 s _59715) (@lem4819593 _110859 R _59714 _59715)). Qed.
Lemma lem4819595 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term564 _110859 s R _59714 _59715) = (term568 _110859 s R _59714 _59715).
Proof. exact (TRANS (@lem4819585 _110859 s R _59714 _59715) (@lem4819594 _110859 s R _59714 _59715)). Qed.
Lemma lem4819596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4819597 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59714 : _110859) (_59715 : _110859) : (term569 _110859 s R _59714 _59715) = (term570 _110859 s R _59714 _59715).
Proof. exact (MK_COMB (@lem4819596) (@lem4819595 _110859 s R _59714 _59715)). Qed.
Lemma lem4819598 {_110859 : Type'} (s : _110859 -> Prop) (_59714 : _110859) : (term79 _110859 s _59714) = (term79 _110859 s _59714).
Proof. exact (eq_refl (term79 _110859 s _59714)). Qed.
Lemma lem4819599 {_110859 : Type'} (R : type1402 _110859) (_59715 : _110859) (s : _110859 -> Prop) (_59714 : _110859) : (term563 _110859 R _59715 s _59714) = (term571 _110859 R _59715 s _59714).
Proof. exact (MK_COMB (@lem4819597 _110859 s R _59714 _59715) (@lem4819598 _110859 s _59714)). Qed.
Lemma lem4819600 {_110859 : Type'} (R : type1402 _110859) (_59715 : _110859) (s : _110859 -> Prop) (_59714 : _110859) : (term456 _110859 s R _59714 _59715) = (term571 _110859 R _59715 s _59714).
Proof. exact (TRANS (@lem4819582 _110859 R _59715 s _59714) (@lem4819599 _110859 R _59715 s _59714)). Qed.
Lemma lem4819602 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : term368 _110859 x y t s R) : term567 _110859 R x y.
Proof. exact (conj (@lem4819572 _110859 x y h1) (@lem4819579 _110859 x y t s R h2)). Qed.
Lemma lem4819603 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : term368 _110859 x y t s R) : term568 _110859 s R x y.
Proof. exact (conj (@lem4819564 _110859 s y h2) (@lem4819602 _110859 x y t s R h1 h3)). Qed.
Lemma lem4819605 {_110859 : Type'} (_59715 : _110859) (_59714 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term571 _110859 R _59715 s _59714.
Proof. exact (EQ_MP (@lem4819600 _110859 R _59715 s _59714) (@lem4817462 _110859 _59714 _59715 x y t s R h1)). Qed.
Lemma lem4819606 {_110859 : Type'} (_59715 : _110859) (_59714 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term571 _110859 R _59715 s _59714.
Proof. exact (@lem4819605 _110859 _59715 _59714 x y t s R h1). Qed.
Lemma lem4819607 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term571 _110859 R y s x.
Proof. exact (@lem4819606 _110859 y x x y t s R h1). Qed.
Lemma lem4819610 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : term368 _110859 x y t s R) : term79 _110859 s x.
Proof. exact (@lem4819607 _110859 x y t s R h3 (@lem4819603 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4819611 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : term368 _110859 x y t s R) : term517 _110859 s x.
Proof. exact (fun h0 : s x => @lem4819610 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4819613 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4819614 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term517 _110859 s x) = (term79 _110859 s x).
Proof. exact (@lem4819613 (s x)). Qed.
Lemma lem4819615 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : term368 _110859 x y t s R) : term79 _110859 s x.
Proof. exact (EQ_MP (@lem4819614 _110859 s x) (@lem4819611 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4819617 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4819618 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4819617 _110859 x y t s R h1). Qed.
Lemma lem4819620 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4819621 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4819620 (R x y)). Qed.
Lemma lem4819622 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4819621 _110859 R x y) (@lem4819618 _110859 x y t s R h1)). Qed.
Lemma lem4819628 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819629 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term463 _110859 t s R _59719 _59718) = (term572 _110859 t s R _59719 _59718).
Proof. exact (@lem4819628 (t _59718) (term79 _110859 s _59718) (term461 _110859 t s R _59719 _59718)). Qed.
Lemma lem4819653 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819654 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term461 _110859 t s R _59719 _59718) = (term573 _110859 s t R _59719 _59718).
Proof. exact (@lem4819653 (s _59719) (term79 _110859 t _59719) (R _59719 _59718)). Qed.
Lemma lem4819668 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4819669 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term550 _110859 t R _59719 _59718) = (term551 _110859 R _59718 t _59719).
Proof. exact (@lem4819668 (R _59719 _59718) (term79 _110859 t _59719)). Qed.
Lemma lem4819675 {_110859 : Type'} (s : _110859 -> Prop) (_59719 : _110859) : (term37 _110859 s _59719) = (term37 _110859 s _59719).
Proof. exact (eq_refl (term37 _110859 s _59719)). Qed.
Lemma lem4819676 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term573 _110859 s t R _59719 _59718) = (term574 _110859 s R _59718 t _59719).
Proof. exact (MK_COMB (@lem4819675 _110859 s _59719) (@lem4819669 _110859 R _59718 t _59719)). Qed.
Lemma lem4819680 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819681 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term574 _110859 s R _59718 t _59719) = (term575 _110859 R _59718 s t _59719).
Proof. exact (@lem4819680 (R _59719 _59718) (s _59719) (term79 _110859 t _59719)). Qed.
Lemma lem4819697 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term573 _110859 s t R _59719 _59718) = (term575 _110859 R _59718 s t _59719).
Proof. exact (TRANS (@lem4819676 _110859 s R _59718 t _59719) (@lem4819681 _110859 R _59718 s t _59719)). Qed.
Lemma lem4819698 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term461 _110859 t s R _59719 _59718) = (term575 _110859 R _59718 s t _59719).
Proof. exact (TRANS (@lem4819654 _110859 s t R _59719 _59718) (@lem4819697 _110859 R _59718 s t _59719)). Qed.
Lemma lem4819699 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) : (term152 _110859 s _59718) = (term152 _110859 s _59718).
Proof. exact (eq_refl (term152 _110859 s _59718)). Qed.
Lemma lem4819700 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term576 _110859 t s R _59719 _59718) = (term577 _110859 R _59718 s t _59719).
Proof. exact (MK_COMB (@lem4819699 _110859 s _59718) (@lem4819698 _110859 R _59718 s t _59719)). Qed.
Lemma lem4819704 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819705 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term577 _110859 R _59718 s t _59719) = (term578 _110859 R _59718 s t _59719).
Proof. exact (@lem4819704 (R _59719 _59718) (term79 _110859 s _59718) (term579 _110859 s t _59719)). Qed.
Lemma lem4819719 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819720 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term580 _110859 _59718 s t _59719) = (term581 _110859 s _59718 t _59719).
Proof. exact (@lem4819719 (s _59719) (term79 _110859 s _59718) (term79 _110859 t _59719)). Qed.
Lemma lem4819736 {_110859 : Type'} (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term484 _110859 R _59719 _59718) = (term484 _110859 R _59719 _59718).
Proof. exact (eq_refl (term484 _110859 R _59719 _59718)). Qed.
Lemma lem4819737 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term578 _110859 R _59718 s t _59719) = (term582 _110859 R s _59718 t _59719).
Proof. exact (MK_COMB (@lem4819736 _110859 R _59719 _59718) (@lem4819720 _110859 s _59718 t _59719)). Qed.
Lemma lem4819748 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term577 _110859 R _59718 s t _59719) = (term582 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819705 _110859 R _59718 s t _59719) (@lem4819737 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819749 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term576 _110859 t s R _59719 _59718) = (term582 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819700 _110859 R _59718 s t _59719) (@lem4819748 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819750 {_110859 : Type'} (t : _110859 -> Prop) (_59718 : _110859) : (term37 _110859 t _59718) = (term37 _110859 t _59718).
Proof. exact (eq_refl (term37 _110859 t _59718)). Qed.
Lemma lem4819751 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term572 _110859 t s R _59719 _59718) = (term583 _110859 R s _59718 t _59719).
Proof. exact (MK_COMB (@lem4819750 _110859 t _59718) (@lem4819749 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819755 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819756 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term583 _110859 R s _59718 t _59719) = (term584 _110859 R s _59718 t _59719).
Proof. exact (@lem4819755 (R _59719 _59718) (t _59718) (term581 _110859 s _59718 t _59719)). Qed.
Lemma lem4819770 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819771 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term585 _110859 s _59718 t _59719) = (term586 _110859 s _59718 t _59719).
Proof. exact (@lem4819770 (s _59719) (t _59718) (term587 _110859 s _59718 t _59719)). Qed.
Lemma lem4819797 {_110859 : Type'} (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term484 _110859 R _59719 _59718) = (term484 _110859 R _59719 _59718).
Proof. exact (eq_refl (term484 _110859 R _59719 _59718)). Qed.
Lemma lem4819798 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term584 _110859 R s _59718 t _59719) = (term588 _110859 R s _59718 t _59719).
Proof. exact (MK_COMB (@lem4819797 _110859 R _59719 _59718) (@lem4819771 _110859 s _59718 t _59719)). Qed.
Lemma lem4819809 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term583 _110859 R s _59718 t _59719) = (term588 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819756 _110859 R s _59718 t _59719) (@lem4819798 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819810 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term572 _110859 t s R _59719 _59718) = (term588 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819751 _110859 R s _59718 t _59719) (@lem4819809 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819811 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term463 _110859 t s R _59719 _59718) = (term588 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819629 _110859 t s R _59719 _59718) (@lem4819810 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4819813 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term589 _110859 t s R _59719 _59718) = (term590 _110859 R s _59718 t _59719).
Proof. exact (MK_COMB (@lem4819812) (@lem4819811 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819837 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819838 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term461 _110859 t s R _59719 _59718) = (term573 _110859 s t R _59719 _59718).
Proof. exact (@lem4819837 (s _59719) (term79 _110859 t _59719) (R _59719 _59718)). Qed.
Lemma lem4819852 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4819853 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term550 _110859 t R _59719 _59718) = (term551 _110859 R _59718 t _59719).
Proof. exact (@lem4819852 (R _59719 _59718) (term79 _110859 t _59719)). Qed.
Lemma lem4819859 {_110859 : Type'} (s : _110859 -> Prop) (_59719 : _110859) : (term37 _110859 s _59719) = (term37 _110859 s _59719).
Proof. exact (eq_refl (term37 _110859 s _59719)). Qed.
Lemma lem4819860 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term573 _110859 s t R _59719 _59718) = (term574 _110859 s R _59718 t _59719).
Proof. exact (MK_COMB (@lem4819859 _110859 s _59719) (@lem4819853 _110859 R _59718 t _59719)). Qed.
Lemma lem4819864 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819865 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term574 _110859 s R _59718 t _59719) = (term575 _110859 R _59718 s t _59719).
Proof. exact (@lem4819864 (R _59719 _59718) (s _59719) (term79 _110859 t _59719)). Qed.
Lemma lem4819881 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term573 _110859 s t R _59719 _59718) = (term575 _110859 R _59718 s t _59719).
Proof. exact (TRANS (@lem4819860 _110859 s R _59718 t _59719) (@lem4819865 _110859 R _59718 s t _59719)). Qed.
Lemma lem4819882 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term461 _110859 t s R _59719 _59718) = (term575 _110859 R _59718 s t _59719).
Proof. exact (TRANS (@lem4819838 _110859 s t R _59719 _59718) (@lem4819881 _110859 R _59718 s t _59719)). Qed.
Lemma lem4819883 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) : (term152 _110859 s _59718) = (term152 _110859 s _59718).
Proof. exact (eq_refl (term152 _110859 s _59718)). Qed.
Lemma lem4819884 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term576 _110859 t s R _59719 _59718) = (term577 _110859 R _59718 s t _59719).
Proof. exact (MK_COMB (@lem4819883 _110859 s _59718) (@lem4819882 _110859 R _59718 s t _59719)). Qed.
Lemma lem4819888 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819889 {_110859 : Type'} (R : type1402 _110859) (_59718 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59719 : _110859) : (term577 _110859 R _59718 s t _59719) = (term578 _110859 R _59718 s t _59719).
Proof. exact (@lem4819888 (R _59719 _59718) (term79 _110859 s _59718) (term579 _110859 s t _59719)). Qed.
Lemma lem4819903 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819904 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term580 _110859 _59718 s t _59719) = (term581 _110859 s _59718 t _59719).
Proof. exact (@lem4819903 (s _59719) (term79 _110859 s _59718) (term79 _110859 t _59719)). Qed.
Lemma lem4819920 {_110859 : Type'} (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term484 _110859 R _59719 _59718) = (term484 _110859 R _59719 _59718).
Proof. exact (eq_refl (term484 _110859 R _59719 _59718)). Qed.
Lemma lem4819921 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term578 _110859 R _59718 s t _59719) = (term582 _110859 R s _59718 t _59719).
Proof. exact (MK_COMB (@lem4819920 _110859 R _59719 _59718) (@lem4819904 _110859 s _59718 t _59719)). Qed.
Lemma lem4819932 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term577 _110859 R _59718 s t _59719) = (term582 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819889 _110859 R _59718 s t _59719) (@lem4819921 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819933 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term576 _110859 t s R _59719 _59718) = (term582 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819884 _110859 R _59718 s t _59719) (@lem4819932 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819934 {_110859 : Type'} (t : _110859 -> Prop) (_59718 : _110859) : (term37 _110859 t _59718) = (term37 _110859 t _59718).
Proof. exact (eq_refl (term37 _110859 t _59718)). Qed.
Lemma lem4819935 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term572 _110859 t s R _59719 _59718) = (term583 _110859 R s _59718 t _59719).
Proof. exact (MK_COMB (@lem4819934 _110859 t _59718) (@lem4819933 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819939 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819940 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term583 _110859 R s _59718 t _59719) = (term584 _110859 R s _59718 t _59719).
Proof. exact (@lem4819939 (R _59719 _59718) (t _59718) (term581 _110859 s _59718 t _59719)). Qed.
Lemma lem4819954 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4819955 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term585 _110859 s _59718 t _59719) = (term586 _110859 s _59718 t _59719).
Proof. exact (@lem4819954 (s _59719) (t _59718) (term587 _110859 s _59718 t _59719)). Qed.
Lemma lem4819981 {_110859 : Type'} (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term484 _110859 R _59719 _59718) = (term484 _110859 R _59719 _59718).
Proof. exact (eq_refl (term484 _110859 R _59719 _59718)). Qed.
Lemma lem4819982 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term584 _110859 R s _59718 t _59719) = (term588 _110859 R s _59718 t _59719).
Proof. exact (MK_COMB (@lem4819981 _110859 R _59719 _59718) (@lem4819955 _110859 s _59718 t _59719)). Qed.
Lemma lem4819993 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term583 _110859 R s _59718 t _59719) = (term588 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819940 _110859 R s _59718 t _59719) (@lem4819982 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819994 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : (term572 _110859 t s R _59719 _59718) = (term588 _110859 R s _59718 t _59719).
Proof. exact (TRANS (@lem4819935 _110859 R s _59718 t _59719) (@lem4819993 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819995 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : ((term463 _110859 t s R _59719 _59718) = (term572 _110859 t s R _59719 _59718)) = ((term588 _110859 R s _59718 t _59719) = (term588 _110859 R s _59718 t _59719)).
Proof. exact (MK_COMB (@lem4819813 _110859 R s _59718 t _59719) (@lem4819994 _110859 R s _59718 t _59719)). Qed.
Lemma lem4819997 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4819998 (x : Prop) : (x = x) = True.
Proof. exact (@lem4819997 Prop x). Qed.
Lemma lem4819999 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59718 : _110859) (t : _110859 -> Prop) (_59719 : _110859) : ((term588 _110859 R s _59718 t _59719) = (term588 _110859 R s _59718 t _59719)) = True.
Proof. exact (@lem4819998 (term588 _110859 R s _59718 t _59719)). Qed.
Lemma lem4820000 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : ((term463 _110859 t s R _59719 _59718) = (term572 _110859 t s R _59719 _59718)) = True.
Proof. exact (TRANS (@lem4819995 _110859 R s _59718 t _59719) (@lem4819999 _110859 R s _59718 t _59719)). Qed.
Lemma lem4820001 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : True = ((term463 _110859 t s R _59719 _59718) = (term572 _110859 t s R _59719 _59718)).
Proof. exact (SYM (@lem4820000 _110859 t s R _59719 _59718)). Qed.
Lemma lem4820002 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term463 _110859 t s R _59719 _59718) = (term572 _110859 t s R _59719 _59718).
Proof. exact (EQ_MP (@lem4820001 _110859 t s R _59719 _59718) (@lem0)). Qed.
Lemma lem4820003 {_110859 : Type'} (_59719 : _110859) (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term572 _110859 t s R _59719 _59718.
Proof. exact (EQ_MP (@lem4820002 _110859 t s R _59719 _59718) (@lem4817536 _110859 _59719 _59718 x y t s R h1)). Qed.
Lemma lem4820005 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4820006 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (t : _110859 -> Prop) (_59718 : _110859) : (term572 _110859 t s R _59719 _59718) = (term591 _110859 s R _59719 t _59718).
Proof. exact (@lem4820005 (term576 _110859 t s R _59719 _59718) (t _59718)). Qed.
Lemma lem4820008 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4820009 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term592 _110859 t s R _59719 _59718) = (term593 _110859 t s R _59719 _59718).
Proof. exact (@lem4820008 (term79 _110859 s _59718) (term461 _110859 t s R _59719 _59718)). Qed.
Lemma lem4820011 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4820012 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) : (term183 _110859 s _59718) = (s _59718).
Proof. exact (@lem4820011 (s _59718)). Qed.
Lemma lem4820013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4820014 {_110859 : Type'} (s : _110859 -> Prop) (_59718 : _110859) : (term500 _110859 s _59718) = (term59 _110859 s _59718).
Proof. exact (MK_COMB (@lem4820013) (@lem4820012 _110859 s _59718)). Qed.
Lemma lem4820016 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4820017 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term594 _110859 t s R _59719 _59718) = (term595 _110859 t s R _59719 _59718).
Proof. exact (@lem4820016 (term79 _110859 t _59719) (term596 _110859 s R _59719 _59718)). Qed.
Lemma lem4820019 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4820020 {_110859 : Type'} (t : _110859 -> Prop) (_59719 : _110859) : (term183 _110859 t _59719) = (t _59719).
Proof. exact (@lem4820019 (t _59719)). Qed.
Lemma lem4820021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4820022 {_110859 : Type'} (t : _110859 -> Prop) (_59719 : _110859) : (term500 _110859 t _59719) = (term59 _110859 t _59719).
Proof. exact (MK_COMB (@lem4820021) (@lem4820020 _110859 t _59719)). Qed.
Lemma lem4820024 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4820025 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term597 _110859 s R _59719 _59718) = (term598 _110859 s R _59719 _59718).
Proof. exact (@lem4820024 (s _59719) (R _59719 _59718)). Qed.
Lemma lem4820026 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term595 _110859 t s R _59719 _59718) = (term599 _110859 t s R _59719 _59718).
Proof. exact (MK_COMB (@lem4820022 _110859 t _59719) (@lem4820025 _110859 s R _59719 _59718)). Qed.
Lemma lem4820027 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term594 _110859 t s R _59719 _59718) = (term599 _110859 t s R _59719 _59718).
Proof. exact (TRANS (@lem4820017 _110859 t s R _59719 _59718) (@lem4820026 _110859 t s R _59719 _59718)). Qed.
Lemma lem4820028 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term593 _110859 t s R _59719 _59718) = (term600 _110859 t s R _59719 _59718).
Proof. exact (MK_COMB (@lem4820014 _110859 s _59718) (@lem4820027 _110859 t s R _59719 _59718)). Qed.
Lemma lem4820029 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term592 _110859 t s R _59719 _59718) = (term600 _110859 t s R _59719 _59718).
Proof. exact (TRANS (@lem4820009 _110859 t s R _59719 _59718) (@lem4820028 _110859 t s R _59719 _59718)). Qed.
Lemma lem4820030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4820031 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (_59718 : _110859) : (term601 _110859 t s R _59719 _59718) = (term602 _110859 t s R _59719 _59718).
Proof. exact (MK_COMB (@lem4820030) (@lem4820029 _110859 t s R _59719 _59718)). Qed.
Lemma lem4820032 {_110859 : Type'} (t : _110859 -> Prop) (_59718 : _110859) : (t _59718) = (t _59718).
Proof. exact (eq_refl (t _59718)). Qed.
Lemma lem4820033 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (t : _110859 -> Prop) (_59718 : _110859) : (term591 _110859 s R _59719 t _59718) = (term603 _110859 s R _59719 t _59718).
Proof. exact (MK_COMB (@lem4820031 _110859 t s R _59719 _59718) (@lem4820032 _110859 t _59718)). Qed.
Lemma lem4820034 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59719 : _110859) (t : _110859 -> Prop) (_59718 : _110859) : (term572 _110859 t s R _59719 _59718) = (term603 _110859 s R _59719 t _59718).
Proof. exact (TRANS (@lem4820006 _110859 s R _59719 t _59718) (@lem4820033 _110859 s R _59719 t _59718)). Qed.
Lemma lem4820036 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : term368 _110859 x y t s R) : term598 _110859 s R x y.
Proof. exact (conj (@lem4819615 _110859 x y t s R h1 h2 h3) (@lem4819622 _110859 x y t s R h3)). Qed.
Lemma lem4820037 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : term599 _110859 t s R x y.
Proof. exact (conj (@lem4819557 _110859 t x h3) (@lem4820036 _110859 x y t s R h1 h2 h4)). Qed.
Lemma lem4820038 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : term600 _110859 t s R x y.
Proof. exact (conj (@lem4819550 _110859 s y h2) (@lem4820037 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4820040 {_110859 : Type'} (_59719 : _110859) (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term603 _110859 s R _59719 t _59718.
Proof. exact (EQ_MP (@lem4820034 _110859 s R _59719 t _59718) (@lem4820003 _110859 _59719 _59718 x y t s R h1)). Qed.
Lemma lem4820041 {_110859 : Type'} (_59719 : _110859) (_59718 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term603 _110859 s R _59719 t _59718.
Proof. exact (@lem4820040 _110859 _59719 _59718 x y t s R h1). Qed.
Lemma lem4820042 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term603 _110859 s R x t y.
Proof. exact (@lem4820041 _110859 x y x y t s R h1). Qed.
Lemma lem4820045 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : t y.
Proof. exact (@lem4820042 _110859 x y t s R h4 (@lem4820038 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4820046 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4820045 _110859 x y t s R h1 h2 h3 h4). Qed.
Lemma lem4820048 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4820049 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4820048 (t y)). Qed.
Lemma lem4820050 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : t y.
Proof. exact (EQ_MP (@lem4820049 _110859 t y) (@lem4820046 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4820052 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4820053 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4820052 _110859 x y t s R h1). Qed.
Lemma lem4820055 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4820056 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4820055 (R x y)). Qed.
Lemma lem4820057 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4820056 _110859 R x y) (@lem4820053 _110859 x y t s R h1)). Qed.
Lemma lem4820073 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820074 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term455 _110859 t R _59716 _59717) = (term473 _110859 t R _59716 _59717).
Proof. exact (@lem4820073 (_59716 = _59717) (term79 _110859 t _59717) (R _59716 _59717)). Qed.
Lemma lem4820090 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4820091 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term474 _110859 t R _59716 _59717) = (term475 _110859 R _59716 t _59717).
Proof. exact (@lem4820090 (R _59716 _59717) (term79 _110859 t _59717)). Qed.
Lemma lem4820097 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) : (term476 _110859 _59716 _59717) = (term476 _110859 _59716 _59717).
Proof. exact (eq_refl (term476 _110859 _59716 _59717)). Qed.
Lemma lem4820098 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term473 _110859 t R _59716 _59717) = (term477 _110859 R _59716 t _59717).
Proof. exact (MK_COMB (@lem4820097 _110859 _59716 _59717) (@lem4820091 _110859 R _59716 t _59717)). Qed.
Lemma lem4820102 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820103 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term477 _110859 R _59716 t _59717) = (term478 _110859 R _59716 t _59717).
Proof. exact (@lem4820102 (R _59716 _59717) (_59716 = _59717) (term79 _110859 t _59717)). Qed.
Lemma lem4820121 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term473 _110859 t R _59716 _59717) = (term478 _110859 R _59716 t _59717).
Proof. exact (TRANS (@lem4820098 _110859 R _59716 t _59717) (@lem4820103 _110859 R _59716 t _59717)). Qed.
Lemma lem4820122 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term455 _110859 t R _59716 _59717) = (term478 _110859 R _59716 t _59717).
Proof. exact (TRANS (@lem4820074 _110859 t R _59716 _59717) (@lem4820121 _110859 R _59716 t _59717)). Qed.
Lemma lem4820123 {_110859 : Type'} (t : _110859 -> Prop) (_59716 : _110859) : (term152 _110859 t _59716) = (term152 _110859 t _59716).
Proof. exact (eq_refl (term152 _110859 t _59716)). Qed.
Lemma lem4820124 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term456 _110859 t R _59716 _59717) = (term479 _110859 R _59716 t _59717).
Proof. exact (MK_COMB (@lem4820123 _110859 t _59716) (@lem4820122 _110859 R _59716 t _59717)). Qed.
Lemma lem4820128 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820129 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term479 _110859 R _59716 t _59717) = (term480 _110859 R _59716 t _59717).
Proof. exact (@lem4820128 (R _59716 _59717) (term79 _110859 t _59716) (term481 _110859 _59716 t _59717)). Qed.
Lemma lem4820143 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820144 {_110859 : Type'} (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term482 _110859 _59716 t _59717) = (term483 _110859 _59716 t _59717).
Proof. exact (@lem4820143 (_59716 = _59717) (term79 _110859 t _59716) (term79 _110859 t _59717)). Qed.
Lemma lem4820162 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term484 _110859 R _59716 _59717) = (term484 _110859 R _59716 _59717).
Proof. exact (eq_refl (term484 _110859 R _59716 _59717)). Qed.
Lemma lem4820163 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term480 _110859 R _59716 t _59717) = (term485 _110859 R _59716 t _59717).
Proof. exact (MK_COMB (@lem4820162 _110859 R _59716 _59717) (@lem4820144 _110859 _59716 t _59717)). Qed.
Lemma lem4820174 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term479 _110859 R _59716 t _59717) = (term485 _110859 R _59716 t _59717).
Proof. exact (TRANS (@lem4820129 _110859 R _59716 t _59717) (@lem4820163 _110859 R _59716 t _59717)). Qed.
Lemma lem4820175 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term456 _110859 t R _59716 _59717) = (term485 _110859 R _59716 t _59717).
Proof. exact (TRANS (@lem4820124 _110859 R _59716 t _59717) (@lem4820174 _110859 R _59716 t _59717)). Qed.
Lemma lem4820176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4820177 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term486 _110859 t R _59716 _59717) = (term487 _110859 R _59716 t _59717).
Proof. exact (MK_COMB (@lem4820176) (@lem4820175 _110859 R _59716 t _59717)). Qed.
Lemma lem4820203 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4820204 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term474 _110859 t R _59716 _59717) = (term475 _110859 R _59716 t _59717).
Proof. exact (@lem4820203 (R _59716 _59717) (term79 _110859 t _59717)). Qed.
Lemma lem4820210 {_110859 : Type'} (t : _110859 -> Prop) (_59716 : _110859) : (term152 _110859 t _59716) = (term152 _110859 t _59716).
Proof. exact (eq_refl (term152 _110859 t _59716)). Qed.
Lemma lem4820211 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term488 _110859 t R _59716 _59717) = (term489 _110859 R _59716 t _59717).
Proof. exact (MK_COMB (@lem4820210 _110859 t _59716) (@lem4820204 _110859 R _59716 t _59717)). Qed.
Lemma lem4820215 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820216 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term489 _110859 R _59716 t _59717) = (term490 _110859 R _59716 t _59717).
Proof. exact (@lem4820215 (R _59716 _59717) (term79 _110859 t _59716) (term79 _110859 t _59717)). Qed.
Lemma lem4820232 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term488 _110859 t R _59716 _59717) = (term490 _110859 R _59716 t _59717).
Proof. exact (TRANS (@lem4820211 _110859 R _59716 t _59717) (@lem4820216 _110859 R _59716 t _59717)). Qed.
Lemma lem4820233 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) : (term476 _110859 _59716 _59717) = (term476 _110859 _59716 _59717).
Proof. exact (eq_refl (term476 _110859 _59716 _59717)). Qed.
Lemma lem4820234 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term491 _110859 t R _59716 _59717) = (term492 _110859 R _59716 t _59717).
Proof. exact (MK_COMB (@lem4820233 _110859 _59716 _59717) (@lem4820232 _110859 R _59716 t _59717)). Qed.
Lemma lem4820238 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820239 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term492 _110859 R _59716 t _59717) = (term485 _110859 R _59716 t _59717).
Proof. exact (@lem4820238 (R _59716 _59717) (_59716 = _59717) (term493 _110859 _59716 t _59717)). Qed.
Lemma lem4820267 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : (term491 _110859 t R _59716 _59717) = (term485 _110859 R _59716 t _59717).
Proof. exact (TRANS (@lem4820234 _110859 R _59716 t _59717) (@lem4820239 _110859 R _59716 t _59717)). Qed.
Lemma lem4820268 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : ((term456 _110859 t R _59716 _59717) = (term491 _110859 t R _59716 _59717)) = ((term485 _110859 R _59716 t _59717) = (term485 _110859 R _59716 t _59717)).
Proof. exact (MK_COMB (@lem4820177 _110859 R _59716 t _59717) (@lem4820267 _110859 R _59716 t _59717)). Qed.
Lemma lem4820270 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4820271 (x : Prop) : (x = x) = True.
Proof. exact (@lem4820270 Prop x). Qed.
Lemma lem4820272 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (t : _110859 -> Prop) (_59717 : _110859) : ((term485 _110859 R _59716 t _59717) = (term485 _110859 R _59716 t _59717)) = True.
Proof. exact (@lem4820271 (term485 _110859 R _59716 t _59717)). Qed.
Lemma lem4820273 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : ((term456 _110859 t R _59716 _59717) = (term491 _110859 t R _59716 _59717)) = True.
Proof. exact (TRANS (@lem4820268 _110859 R _59716 t _59717) (@lem4820272 _110859 R _59716 t _59717)). Qed.
Lemma lem4820274 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : True = ((term456 _110859 t R _59716 _59717) = (term491 _110859 t R _59716 _59717)).
Proof. exact (SYM (@lem4820273 _110859 t R _59716 _59717)). Qed.
Lemma lem4820275 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term456 _110859 t R _59716 _59717) = (term491 _110859 t R _59716 _59717).
Proof. exact (EQ_MP (@lem4820274 _110859 t R _59716 _59717) (@lem0)). Qed.
Lemma lem4820276 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term491 _110859 t R _59716 _59717.
Proof. exact (EQ_MP (@lem4820275 _110859 t R _59716 _59717) (@lem4817480 _110859 _59716 _59717 x y t s R h1)). Qed.
Lemma lem4820278 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4820279 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term491 _110859 t R _59716 _59717) = (term495 _110859 t R _59716 _59717).
Proof. exact (@lem4820278 (term488 _110859 t R _59716 _59717) (_59716 = _59717)). Qed.
Lemma lem4820281 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4820282 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term498 _110859 t R _59716 _59717) = (term499 _110859 t R _59716 _59717).
Proof. exact (@lem4820281 (term79 _110859 t _59716) (term474 _110859 t R _59716 _59717)). Qed.
Lemma lem4820284 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4820285 {_110859 : Type'} (t : _110859 -> Prop) (_59716 : _110859) : (term183 _110859 t _59716) = (t _59716).
Proof. exact (@lem4820284 (t _59716)). Qed.
Lemma lem4820286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4820287 {_110859 : Type'} (t : _110859 -> Prop) (_59716 : _110859) : (term500 _110859 t _59716) = (term59 _110859 t _59716).
Proof. exact (MK_COMB (@lem4820286) (@lem4820285 _110859 t _59716)). Qed.
Lemma lem4820289 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4820290 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term501 _110859 t R _59716 _59717) = (term502 _110859 t R _59716 _59717).
Proof. exact (@lem4820289 (term79 _110859 t _59717) (R _59716 _59717)). Qed.
Lemma lem4820292 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4820293 {_110859 : Type'} (t : _110859 -> Prop) (_59717 : _110859) : (term183 _110859 t _59717) = (t _59717).
Proof. exact (@lem4820292 (t _59717)). Qed.
Lemma lem4820294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4820295 {_110859 : Type'} (t : _110859 -> Prop) (_59717 : _110859) : (term500 _110859 t _59717) = (term59 _110859 t _59717).
Proof. exact (MK_COMB (@lem4820294) (@lem4820293 _110859 t _59717)). Qed.
Lemma lem4820296 {_110859 : Type'} (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term438 _110859 R _59716 _59717) = (term438 _110859 R _59716 _59717).
Proof. exact (eq_refl (term438 _110859 R _59716 _59717)). Qed.
Lemma lem4820297 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term502 _110859 t R _59716 _59717) = (term503 _110859 t R _59716 _59717).
Proof. exact (MK_COMB (@lem4820295 _110859 t _59717) (@lem4820296 _110859 R _59716 _59717)). Qed.
Lemma lem4820298 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term501 _110859 t R _59716 _59717) = (term503 _110859 t R _59716 _59717).
Proof. exact (TRANS (@lem4820290 _110859 t R _59716 _59717) (@lem4820297 _110859 t R _59716 _59717)). Qed.
Lemma lem4820299 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term499 _110859 t R _59716 _59717) = (term504 _110859 t R _59716 _59717).
Proof. exact (MK_COMB (@lem4820287 _110859 t _59716) (@lem4820298 _110859 t R _59716 _59717)). Qed.
Lemma lem4820300 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term498 _110859 t R _59716 _59717) = (term504 _110859 t R _59716 _59717).
Proof. exact (TRANS (@lem4820282 _110859 t R _59716 _59717) (@lem4820299 _110859 t R _59716 _59717)). Qed.
Lemma lem4820301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4820302 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term505 _110859 t R _59716 _59717) = (term506 _110859 t R _59716 _59717).
Proof. exact (MK_COMB (@lem4820301) (@lem4820300 _110859 t R _59716 _59717)). Qed.
Lemma lem4820303 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) : (_59716 = _59717) = (_59716 = _59717).
Proof. exact (eq_refl (_59716 = _59717)). Qed.
Lemma lem4820304 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term495 _110859 t R _59716 _59717) = (term507 _110859 t R _59716 _59717).
Proof. exact (MK_COMB (@lem4820302 _110859 t R _59716 _59717) (@lem4820303 _110859 _59716 _59717)). Qed.
Lemma lem4820305 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59716 : _110859) (_59717 : _110859) : (term491 _110859 t R _59716 _59717) = (term507 _110859 t R _59716 _59717).
Proof. exact (TRANS (@lem4820279 _110859 t R _59716 _59717) (@lem4820304 _110859 t R _59716 _59717)). Qed.
Lemma lem4820307 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : term503 _110859 t R x y.
Proof. exact (conj (@lem4820050 _110859 x y t s R h1 h2 h3 h4) (@lem4820057 _110859 x y t s R h4)). Qed.
Lemma lem4820308 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : term504 _110859 t R x y.
Proof. exact (conj (@lem4819543 _110859 t x h3) (@lem4820307 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4820310 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R _59716 _59717.
Proof. exact (EQ_MP (@lem4820305 _110859 t R _59716 _59717) (@lem4820276 _110859 _59716 _59717 x y t s R h1)). Qed.
Lemma lem4820311 {_110859 : Type'} (_59716 : _110859) (_59717 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R _59716 _59717.
Proof. exact (@lem4820310 _110859 _59716 _59717 x y t s R h1). Qed.
Lemma lem4820312 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R x y.
Proof. exact (@lem4820311 _110859 x y x y t s R h1). Qed.
Lemma lem4820315 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s y) (h3 : t x) (h4 : term368 _110859 x y t s R) : x = y.
Proof. exact (@lem4820312 _110859 x y t s R h4 (@lem4820308 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4820316 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : term508 _110859 x y.
Proof. exact (fun h0 : term41 _110859 x y => @lem4820315 _110859 x y t s R h0 h1 h2 h3). Qed.
Lemma lem4820318 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4820319 {_110859 : Type'} (x : _110859) (y : _110859) : (term508 _110859 x y) = (x = y).
Proof. exact (@lem4820318 (x = y)). Qed.
Lemma lem4820320 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : x = y.
Proof. exact (EQ_MP (@lem4820319 _110859 x y) (@lem4820316 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4820323 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4820325 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term509 _110859 x y).
Proof. exact (@lem4820323 (x = y)). Qed.
Lemma lem4820328 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term509 _110859 x y.
Proof. exact (EQ_MP (@lem4820325 _110859 x y) (@lem4817484 _110859 x y t s R h1)). Qed.
Lemma lem4820331 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (@lem4820328 _110859 x y t s R h3 (@lem4820320 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4820332 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : term510.
Proof. exact (fun h0 : ~ False => @lem4820331 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4820334 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4820335 : term510 = False.
Proof. exact (@lem4820334 False). Qed.
Lemma lem4820336 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4820335) (@lem4820332 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4820383 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4820384 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : term469 _110859 s x.
Proof. exact (fun h0 : term79 _110859 s x => @lem4820383 _110859 s x h1). Qed.
Lemma lem4820386 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4820387 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term469 _110859 s x) = (s x).
Proof. exact (@lem4820386 (s x)). Qed.
Lemma lem4820388 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4820387 _110859 s x) (@lem4820384 _110859 s x h1)). Qed.
Lemma lem4820390 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (h1). Qed.
Lemma lem4820391 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4820390 _110859 t y h1). Qed.
Lemma lem4820393 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4820394 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4820393 (t y)). Qed.
Lemma lem4820395 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (EQ_MP (@lem4820394 _110859 t y) (@lem4820391 _110859 t y h1)). Qed.
Lemma lem4820397 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4820398 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : term469 _110859 s x.
Proof. exact (fun h0 : term79 _110859 s x => @lem4820397 _110859 s x h1). Qed.
Lemma lem4820400 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4820401 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) : (term469 _110859 s x) = (s x).
Proof. exact (@lem4820400 (s x)). Qed.
Lemma lem4820402 {_110859 : Type'} (s : _110859 -> Prop) (x : _110859) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4820401 _110859 s x) (@lem4820398 _110859 s x h1)). Qed.
Lemma lem4820405 {_110859 : Type'} (x : _110859) (y : _110859) (h1 : term41 _110859 x y) : term41 _110859 x y.
Proof. exact (h1). Qed.
Lemma lem4820406 {_110859 : Type'} (x : _110859) (y : _110859) (h1 : term41 _110859 x y) : term526 _110859 x y.
Proof. exact (fun h0 : x = y => @lem4820405 _110859 x y h1). Qed.
Lemma lem4820408 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4820409 {_110859 : Type'} (x : _110859) (y : _110859) : (term526 _110859 x y) = (term41 _110859 x y).
Proof. exact (@lem4820408 (x = y)). Qed.
Lemma lem4820410 {_110859 : Type'} (x : _110859) (y : _110859) (h1 : term41 _110859 x y) : term41 _110859 x y.
Proof. exact (EQ_MP (@lem4820409 _110859 x y) (@lem4820406 _110859 x y h1)). Qed.
Lemma lem4820412 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4820413 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4820412 _110859 x y t s R h1). Qed.
Lemma lem4820415 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4820416 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4820415 (R x y)). Qed.
Lemma lem4820417 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4820416 _110859 R x y) (@lem4820413 _110859 x y t s R h1)). Qed.
Lemma lem4820433 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820434 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term455 _110859 s R _59720 _59721) = (term473 _110859 s R _59720 _59721).
Proof. exact (@lem4820433 (_59720 = _59721) (term79 _110859 s _59721) (R _59720 _59721)). Qed.
Lemma lem4820450 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4820451 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term474 _110859 s R _59720 _59721) = (term475 _110859 R _59720 s _59721).
Proof. exact (@lem4820450 (R _59720 _59721) (term79 _110859 s _59721)). Qed.
Lemma lem4820457 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) : (term476 _110859 _59720 _59721) = (term476 _110859 _59720 _59721).
Proof. exact (eq_refl (term476 _110859 _59720 _59721)). Qed.
Lemma lem4820458 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term473 _110859 s R _59720 _59721) = (term477 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820457 _110859 _59720 _59721) (@lem4820451 _110859 R _59720 s _59721)). Qed.
Lemma lem4820462 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820463 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term477 _110859 R _59720 s _59721) = (term478 _110859 R _59720 s _59721).
Proof. exact (@lem4820462 (R _59720 _59721) (_59720 = _59721) (term79 _110859 s _59721)). Qed.
Lemma lem4820481 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term473 _110859 s R _59720 _59721) = (term478 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820458 _110859 R _59720 s _59721) (@lem4820463 _110859 R _59720 s _59721)). Qed.
Lemma lem4820482 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term455 _110859 s R _59720 _59721) = (term478 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820434 _110859 s R _59720 _59721) (@lem4820481 _110859 R _59720 s _59721)). Qed.
Lemma lem4820483 {_110859 : Type'} (s : _110859 -> Prop) (_59720 : _110859) : (term152 _110859 s _59720) = (term152 _110859 s _59720).
Proof. exact (eq_refl (term152 _110859 s _59720)). Qed.
Lemma lem4820484 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term456 _110859 s R _59720 _59721) = (term479 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820483 _110859 s _59720) (@lem4820482 _110859 R _59720 s _59721)). Qed.
Lemma lem4820488 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820489 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term479 _110859 R _59720 s _59721) = (term480 _110859 R _59720 s _59721).
Proof. exact (@lem4820488 (R _59720 _59721) (term79 _110859 s _59720) (term481 _110859 _59720 s _59721)). Qed.
Lemma lem4820503 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820504 {_110859 : Type'} (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term482 _110859 _59720 s _59721) = (term483 _110859 _59720 s _59721).
Proof. exact (@lem4820503 (_59720 = _59721) (term79 _110859 s _59720) (term79 _110859 s _59721)). Qed.
Lemma lem4820522 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term484 _110859 R _59720 _59721) = (term484 _110859 R _59720 _59721).
Proof. exact (eq_refl (term484 _110859 R _59720 _59721)). Qed.
Lemma lem4820523 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term480 _110859 R _59720 s _59721) = (term485 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820522 _110859 R _59720 _59721) (@lem4820504 _110859 _59720 s _59721)). Qed.
Lemma lem4820534 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term479 _110859 R _59720 s _59721) = (term485 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820489 _110859 R _59720 s _59721) (@lem4820523 _110859 R _59720 s _59721)). Qed.
Lemma lem4820535 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term456 _110859 s R _59720 _59721) = (term485 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820484 _110859 R _59720 s _59721) (@lem4820534 _110859 R _59720 s _59721)). Qed.
Lemma lem4820536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4820537 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term486 _110859 s R _59720 _59721) = (term487 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820536) (@lem4820535 _110859 R _59720 s _59721)). Qed.
Lemma lem4820541 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820542 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term604 _110859 s R _59720 _59721) = (term456 _110859 s R _59720 _59721).
Proof. exact (@lem4820541 (term79 _110859 s _59720) (term79 _110859 s _59721) (term547 _110859 R _59720 _59721)). Qed.
Lemma lem4820556 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820557 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term455 _110859 s R _59720 _59721) = (term473 _110859 s R _59720 _59721).
Proof. exact (@lem4820556 (_59720 = _59721) (term79 _110859 s _59721) (R _59720 _59721)). Qed.
Lemma lem4820573 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4820574 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term474 _110859 s R _59720 _59721) = (term475 _110859 R _59720 s _59721).
Proof. exact (@lem4820573 (R _59720 _59721) (term79 _110859 s _59721)). Qed.
Lemma lem4820580 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) : (term476 _110859 _59720 _59721) = (term476 _110859 _59720 _59721).
Proof. exact (eq_refl (term476 _110859 _59720 _59721)). Qed.
Lemma lem4820581 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term473 _110859 s R _59720 _59721) = (term477 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820580 _110859 _59720 _59721) (@lem4820574 _110859 R _59720 s _59721)). Qed.
Lemma lem4820585 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820586 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term477 _110859 R _59720 s _59721) = (term478 _110859 R _59720 s _59721).
Proof. exact (@lem4820585 (R _59720 _59721) (_59720 = _59721) (term79 _110859 s _59721)). Qed.
Lemma lem4820604 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term473 _110859 s R _59720 _59721) = (term478 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820581 _110859 R _59720 s _59721) (@lem4820586 _110859 R _59720 s _59721)). Qed.
Lemma lem4820605 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term455 _110859 s R _59720 _59721) = (term478 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820557 _110859 s R _59720 _59721) (@lem4820604 _110859 R _59720 s _59721)). Qed.
Lemma lem4820606 {_110859 : Type'} (s : _110859 -> Prop) (_59720 : _110859) : (term152 _110859 s _59720) = (term152 _110859 s _59720).
Proof. exact (eq_refl (term152 _110859 s _59720)). Qed.
Lemma lem4820607 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term456 _110859 s R _59720 _59721) = (term479 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820606 _110859 s _59720) (@lem4820605 _110859 R _59720 s _59721)). Qed.
Lemma lem4820611 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820612 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term479 _110859 R _59720 s _59721) = (term480 _110859 R _59720 s _59721).
Proof. exact (@lem4820611 (R _59720 _59721) (term79 _110859 s _59720) (term481 _110859 _59720 s _59721)). Qed.
Lemma lem4820626 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820627 {_110859 : Type'} (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term482 _110859 _59720 s _59721) = (term483 _110859 _59720 s _59721).
Proof. exact (@lem4820626 (_59720 = _59721) (term79 _110859 s _59720) (term79 _110859 s _59721)). Qed.
Lemma lem4820645 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term484 _110859 R _59720 _59721) = (term484 _110859 R _59720 _59721).
Proof. exact (eq_refl (term484 _110859 R _59720 _59721)). Qed.
Lemma lem4820646 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term480 _110859 R _59720 s _59721) = (term485 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820645 _110859 R _59720 _59721) (@lem4820627 _110859 _59720 s _59721)). Qed.
Lemma lem4820657 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term479 _110859 R _59720 s _59721) = (term485 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820612 _110859 R _59720 s _59721) (@lem4820646 _110859 R _59720 s _59721)). Qed.
Lemma lem4820658 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term456 _110859 s R _59720 _59721) = (term485 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820607 _110859 R _59720 s _59721) (@lem4820657 _110859 R _59720 s _59721)). Qed.
Lemma lem4820659 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term604 _110859 s R _59720 _59721) = (term485 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820542 _110859 s R _59720 _59721) (@lem4820658 _110859 R _59720 s _59721)). Qed.
Lemma lem4820660 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : ((term456 _110859 s R _59720 _59721) = (term604 _110859 s R _59720 _59721)) = ((term485 _110859 R _59720 s _59721) = (term485 _110859 R _59720 s _59721)).
Proof. exact (MK_COMB (@lem4820537 _110859 R _59720 s _59721) (@lem4820659 _110859 R _59720 s _59721)). Qed.
Lemma lem4820662 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4820663 (x : Prop) : (x = x) = True.
Proof. exact (@lem4820662 Prop x). Qed.
Lemma lem4820664 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : ((term485 _110859 R _59720 s _59721) = (term485 _110859 R _59720 s _59721)) = True.
Proof. exact (@lem4820663 (term485 _110859 R _59720 s _59721)). Qed.
Lemma lem4820665 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : ((term456 _110859 s R _59720 _59721) = (term604 _110859 s R _59720 _59721)) = True.
Proof. exact (TRANS (@lem4820660 _110859 R _59720 s _59721) (@lem4820664 _110859 R _59720 s _59721)). Qed.
Lemma lem4820666 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : True = ((term456 _110859 s R _59720 _59721) = (term604 _110859 s R _59720 _59721)).
Proof. exact (SYM (@lem4820665 _110859 s R _59720 _59721)). Qed.
Lemma lem4820667 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term456 _110859 s R _59720 _59721) = (term604 _110859 s R _59720 _59721).
Proof. exact (EQ_MP (@lem4820666 _110859 s R _59720 _59721) (@lem0)). Qed.
Lemma lem4820668 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term604 _110859 s R _59720 _59721.
Proof. exact (EQ_MP (@lem4820667 _110859 s R _59720 _59721) (@lem4817554 _110859 _59720 _59721 x y t s R h1)). Qed.
Lemma lem4820670 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4820671 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term604 _110859 s R _59720 _59721) = (term605 _110859 R _59720 s _59721).
Proof. exact (@lem4820670 (term548 _110859 s R _59720 _59721) (term79 _110859 s _59721)). Qed.
Lemma lem4820673 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4820674 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term606 _110859 s R _59720 _59721) = (term607 _110859 s R _59720 _59721).
Proof. exact (@lem4820673 (term79 _110859 s _59720) (term547 _110859 R _59720 _59721)). Qed.
Lemma lem4820676 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4820677 {_110859 : Type'} (s : _110859 -> Prop) (_59720 : _110859) : (term183 _110859 s _59720) = (s _59720).
Proof. exact (@lem4820676 (s _59720)). Qed.
Lemma lem4820678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4820679 {_110859 : Type'} (s : _110859 -> Prop) (_59720 : _110859) : (term500 _110859 s _59720) = (term59 _110859 s _59720).
Proof. exact (MK_COMB (@lem4820678) (@lem4820677 _110859 s _59720)). Qed.
Lemma lem4820681 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4820682 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term566 _110859 R _59720 _59721) = (term567 _110859 R _59720 _59721).
Proof. exact (@lem4820681 (_59720 = _59721) (R _59720 _59721)). Qed.
Lemma lem4820683 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term607 _110859 s R _59720 _59721) = (term608 _110859 s R _59720 _59721).
Proof. exact (MK_COMB (@lem4820679 _110859 s _59720) (@lem4820682 _110859 R _59720 _59721)). Qed.
Lemma lem4820684 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term606 _110859 s R _59720 _59721) = (term608 _110859 s R _59720 _59721).
Proof. exact (TRANS (@lem4820674 _110859 s R _59720 _59721) (@lem4820683 _110859 s R _59720 _59721)). Qed.
Lemma lem4820685 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4820686 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59720 : _110859) (_59721 : _110859) : (term609 _110859 s R _59720 _59721) = (term610 _110859 s R _59720 _59721).
Proof. exact (MK_COMB (@lem4820685) (@lem4820684 _110859 s R _59720 _59721)). Qed.
Lemma lem4820687 {_110859 : Type'} (s : _110859 -> Prop) (_59721 : _110859) : (term79 _110859 s _59721) = (term79 _110859 s _59721).
Proof. exact (eq_refl (term79 _110859 s _59721)). Qed.
Lemma lem4820688 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term605 _110859 R _59720 s _59721) = (term611 _110859 R _59720 s _59721).
Proof. exact (MK_COMB (@lem4820686 _110859 s R _59720 _59721) (@lem4820687 _110859 s _59721)). Qed.
Lemma lem4820689 {_110859 : Type'} (R : type1402 _110859) (_59720 : _110859) (s : _110859 -> Prop) (_59721 : _110859) : (term604 _110859 s R _59720 _59721) = (term611 _110859 R _59720 s _59721).
Proof. exact (TRANS (@lem4820671 _110859 R _59720 s _59721) (@lem4820688 _110859 R _59720 s _59721)). Qed.
Lemma lem4820691 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : term368 _110859 x y t s R) : term567 _110859 R x y.
Proof. exact (conj (@lem4820410 _110859 x y h1) (@lem4820417 _110859 x y t s R h2)). Qed.
Lemma lem4820692 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : term368 _110859 x y t s R) : term608 _110859 s R x y.
Proof. exact (conj (@lem4820402 _110859 s x h2) (@lem4820691 _110859 x y t s R h1 h3)). Qed.
Lemma lem4820694 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term611 _110859 R _59720 s _59721.
Proof. exact (EQ_MP (@lem4820689 _110859 R _59720 s _59721) (@lem4820668 _110859 _59720 _59721 x y t s R h1)). Qed.
Lemma lem4820695 {_110859 : Type'} (_59720 : _110859) (_59721 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term611 _110859 R _59720 s _59721.
Proof. exact (@lem4820694 _110859 _59720 _59721 x y t s R h1). Qed.
Lemma lem4820696 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term611 _110859 R x s y.
Proof. exact (@lem4820695 _110859 x y x y t s R h1). Qed.
Lemma lem4820699 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : term368 _110859 x y t s R) : term79 _110859 s y.
Proof. exact (@lem4820696 _110859 x y t s R h3 (@lem4820692 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4820700 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : term368 _110859 x y t s R) : term517 _110859 s y.
Proof. exact (fun h0 : s y => @lem4820699 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4820702 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4820703 {_110859 : Type'} (s : _110859 -> Prop) (y : _110859) : (term517 _110859 s y) = (term79 _110859 s y).
Proof. exact (@lem4820702 (s y)). Qed.
Lemma lem4820704 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : term368 _110859 x y t s R) : term79 _110859 s y.
Proof. exact (EQ_MP (@lem4820703 _110859 s y) (@lem4820700 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4820706 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4820707 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4820706 _110859 x y t s R h1). Qed.
Lemma lem4820709 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4820710 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4820709 (R x y)). Qed.
Lemma lem4820711 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4820710 _110859 R x y) (@lem4820707 _110859 x y t s R h1)). Qed.
Lemma lem4820717 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820718 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term468 _110859 t s R _59724 _59725) = (term612 _110859 t s R _59724 _59725).
Proof. exact (@lem4820717 (t _59724) (term79 _110859 s _59724) (term466 _110859 t s R _59724 _59725)). Qed.
Lemma lem4820742 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820743 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term466 _110859 t s R _59724 _59725) = (term613 _110859 s t R _59724 _59725).
Proof. exact (@lem4820742 (s _59725) (term79 _110859 t _59725) (R _59724 _59725)). Qed.
Lemma lem4820757 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4820758 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term474 _110859 t R _59724 _59725) = (term475 _110859 R _59724 t _59725).
Proof. exact (@lem4820757 (R _59724 _59725) (term79 _110859 t _59725)). Qed.
Lemma lem4820764 {_110859 : Type'} (s : _110859 -> Prop) (_59725 : _110859) : (term37 _110859 s _59725) = (term37 _110859 s _59725).
Proof. exact (eq_refl (term37 _110859 s _59725)). Qed.
Lemma lem4820765 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term613 _110859 s t R _59724 _59725) = (term614 _110859 s R _59724 t _59725).
Proof. exact (MK_COMB (@lem4820764 _110859 s _59725) (@lem4820758 _110859 R _59724 t _59725)). Qed.
Lemma lem4820769 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820770 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term614 _110859 s R _59724 t _59725) = (term615 _110859 R _59724 s t _59725).
Proof. exact (@lem4820769 (R _59724 _59725) (s _59725) (term79 _110859 t _59725)). Qed.
Lemma lem4820786 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term613 _110859 s t R _59724 _59725) = (term615 _110859 R _59724 s t _59725).
Proof. exact (TRANS (@lem4820765 _110859 s R _59724 t _59725) (@lem4820770 _110859 R _59724 s t _59725)). Qed.
Lemma lem4820787 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term466 _110859 t s R _59724 _59725) = (term615 _110859 R _59724 s t _59725).
Proof. exact (TRANS (@lem4820743 _110859 s t R _59724 _59725) (@lem4820786 _110859 R _59724 s t _59725)). Qed.
Lemma lem4820788 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) : (term152 _110859 s _59724) = (term152 _110859 s _59724).
Proof. exact (eq_refl (term152 _110859 s _59724)). Qed.
Lemma lem4820789 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term616 _110859 t s R _59724 _59725) = (term617 _110859 R _59724 s t _59725).
Proof. exact (MK_COMB (@lem4820788 _110859 s _59724) (@lem4820787 _110859 R _59724 s t _59725)). Qed.
Lemma lem4820793 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820794 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term617 _110859 R _59724 s t _59725) = (term618 _110859 R _59724 s t _59725).
Proof. exact (@lem4820793 (R _59724 _59725) (term79 _110859 s _59724) (term579 _110859 s t _59725)). Qed.
Lemma lem4820808 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820809 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term580 _110859 _59724 s t _59725) = (term581 _110859 s _59724 t _59725).
Proof. exact (@lem4820808 (s _59725) (term79 _110859 s _59724) (term79 _110859 t _59725)). Qed.
Lemma lem4820825 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term484 _110859 R _59724 _59725) = (term484 _110859 R _59724 _59725).
Proof. exact (eq_refl (term484 _110859 R _59724 _59725)). Qed.
Lemma lem4820826 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term618 _110859 R _59724 s t _59725) = (term619 _110859 R s _59724 t _59725).
Proof. exact (MK_COMB (@lem4820825 _110859 R _59724 _59725) (@lem4820809 _110859 s _59724 t _59725)). Qed.
Lemma lem4820837 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term617 _110859 R _59724 s t _59725) = (term619 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4820794 _110859 R _59724 s t _59725) (@lem4820826 _110859 R s _59724 t _59725)). Qed.
Lemma lem4820838 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term616 _110859 t s R _59724 _59725) = (term619 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4820789 _110859 R _59724 s t _59725) (@lem4820837 _110859 R s _59724 t _59725)). Qed.
Lemma lem4820839 {_110859 : Type'} (t : _110859 -> Prop) (_59724 : _110859) : (term37 _110859 t _59724) = (term37 _110859 t _59724).
Proof. exact (eq_refl (term37 _110859 t _59724)). Qed.
Lemma lem4820840 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term612 _110859 t s R _59724 _59725) = (term620 _110859 R s _59724 t _59725).
Proof. exact (MK_COMB (@lem4820839 _110859 t _59724) (@lem4820838 _110859 R s _59724 t _59725)). Qed.
Lemma lem4820844 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820845 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term620 _110859 R s _59724 t _59725) = (term621 _110859 R s _59724 t _59725).
Proof. exact (@lem4820844 (R _59724 _59725) (t _59724) (term581 _110859 s _59724 t _59725)). Qed.
Lemma lem4820859 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820860 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term585 _110859 s _59724 t _59725) = (term586 _110859 s _59724 t _59725).
Proof. exact (@lem4820859 (s _59725) (t _59724) (term587 _110859 s _59724 t _59725)). Qed.
Lemma lem4820886 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term484 _110859 R _59724 _59725) = (term484 _110859 R _59724 _59725).
Proof. exact (eq_refl (term484 _110859 R _59724 _59725)). Qed.
Lemma lem4820887 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term621 _110859 R s _59724 t _59725) = (term622 _110859 R s _59724 t _59725).
Proof. exact (MK_COMB (@lem4820886 _110859 R _59724 _59725) (@lem4820860 _110859 s _59724 t _59725)). Qed.
Lemma lem4820898 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term620 _110859 R s _59724 t _59725) = (term622 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4820845 _110859 R s _59724 t _59725) (@lem4820887 _110859 R s _59724 t _59725)). Qed.
Lemma lem4820899 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term612 _110859 t s R _59724 _59725) = (term622 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4820840 _110859 R s _59724 t _59725) (@lem4820898 _110859 R s _59724 t _59725)). Qed.
Lemma lem4820900 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term468 _110859 t s R _59724 _59725) = (term622 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4820718 _110859 t s R _59724 _59725) (@lem4820899 _110859 R s _59724 t _59725)). Qed.
Lemma lem4820901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4820902 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term623 _110859 t s R _59724 _59725) = (term624 _110859 R s _59724 t _59725).
Proof. exact (MK_COMB (@lem4820901) (@lem4820900 _110859 R s _59724 t _59725)). Qed.
Lemma lem4820926 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820927 {_110859 : Type'} (s : _110859 -> Prop) (t : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term466 _110859 t s R _59724 _59725) = (term613 _110859 s t R _59724 _59725).
Proof. exact (@lem4820926 (s _59725) (term79 _110859 t _59725) (R _59724 _59725)). Qed.
Lemma lem4820941 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4820942 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term474 _110859 t R _59724 _59725) = (term475 _110859 R _59724 t _59725).
Proof. exact (@lem4820941 (R _59724 _59725) (term79 _110859 t _59725)). Qed.
Lemma lem4820948 {_110859 : Type'} (s : _110859 -> Prop) (_59725 : _110859) : (term37 _110859 s _59725) = (term37 _110859 s _59725).
Proof. exact (eq_refl (term37 _110859 s _59725)). Qed.
Lemma lem4820949 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term613 _110859 s t R _59724 _59725) = (term614 _110859 s R _59724 t _59725).
Proof. exact (MK_COMB (@lem4820948 _110859 s _59725) (@lem4820942 _110859 R _59724 t _59725)). Qed.
Lemma lem4820953 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820954 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term614 _110859 s R _59724 t _59725) = (term615 _110859 R _59724 s t _59725).
Proof. exact (@lem4820953 (R _59724 _59725) (s _59725) (term79 _110859 t _59725)). Qed.
Lemma lem4820970 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term613 _110859 s t R _59724 _59725) = (term615 _110859 R _59724 s t _59725).
Proof. exact (TRANS (@lem4820949 _110859 s R _59724 t _59725) (@lem4820954 _110859 R _59724 s t _59725)). Qed.
Lemma lem4820971 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term466 _110859 t s R _59724 _59725) = (term615 _110859 R _59724 s t _59725).
Proof. exact (TRANS (@lem4820927 _110859 s t R _59724 _59725) (@lem4820970 _110859 R _59724 s t _59725)). Qed.
Lemma lem4820972 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) : (term152 _110859 s _59724) = (term152 _110859 s _59724).
Proof. exact (eq_refl (term152 _110859 s _59724)). Qed.
Lemma lem4820973 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term616 _110859 t s R _59724 _59725) = (term617 _110859 R _59724 s t _59725).
Proof. exact (MK_COMB (@lem4820972 _110859 s _59724) (@lem4820971 _110859 R _59724 s t _59725)). Qed.
Lemma lem4820977 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820978 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (s : _110859 -> Prop) (t : _110859 -> Prop) (_59725 : _110859) : (term617 _110859 R _59724 s t _59725) = (term618 _110859 R _59724 s t _59725).
Proof. exact (@lem4820977 (R _59724 _59725) (term79 _110859 s _59724) (term579 _110859 s t _59725)). Qed.
Lemma lem4820992 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4820993 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term580 _110859 _59724 s t _59725) = (term581 _110859 s _59724 t _59725).
Proof. exact (@lem4820992 (s _59725) (term79 _110859 s _59724) (term79 _110859 t _59725)). Qed.
Lemma lem4821009 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term484 _110859 R _59724 _59725) = (term484 _110859 R _59724 _59725).
Proof. exact (eq_refl (term484 _110859 R _59724 _59725)). Qed.
Lemma lem4821010 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term618 _110859 R _59724 s t _59725) = (term619 _110859 R s _59724 t _59725).
Proof. exact (MK_COMB (@lem4821009 _110859 R _59724 _59725) (@lem4820993 _110859 s _59724 t _59725)). Qed.
Lemma lem4821021 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term617 _110859 R _59724 s t _59725) = (term619 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4820978 _110859 R _59724 s t _59725) (@lem4821010 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821022 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term616 _110859 t s R _59724 _59725) = (term619 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4820973 _110859 R _59724 s t _59725) (@lem4821021 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821023 {_110859 : Type'} (t : _110859 -> Prop) (_59724 : _110859) : (term37 _110859 t _59724) = (term37 _110859 t _59724).
Proof. exact (eq_refl (term37 _110859 t _59724)). Qed.
Lemma lem4821024 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term612 _110859 t s R _59724 _59725) = (term620 _110859 R s _59724 t _59725).
Proof. exact (MK_COMB (@lem4821023 _110859 t _59724) (@lem4821022 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821028 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821029 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term620 _110859 R s _59724 t _59725) = (term621 _110859 R s _59724 t _59725).
Proof. exact (@lem4821028 (R _59724 _59725) (t _59724) (term581 _110859 s _59724 t _59725)). Qed.
Lemma lem4821043 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821044 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term585 _110859 s _59724 t _59725) = (term586 _110859 s _59724 t _59725).
Proof. exact (@lem4821043 (s _59725) (t _59724) (term587 _110859 s _59724 t _59725)). Qed.
Lemma lem4821070 {_110859 : Type'} (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term484 _110859 R _59724 _59725) = (term484 _110859 R _59724 _59725).
Proof. exact (eq_refl (term484 _110859 R _59724 _59725)). Qed.
Lemma lem4821071 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term621 _110859 R s _59724 t _59725) = (term622 _110859 R s _59724 t _59725).
Proof. exact (MK_COMB (@lem4821070 _110859 R _59724 _59725) (@lem4821044 _110859 s _59724 t _59725)). Qed.
Lemma lem4821082 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term620 _110859 R s _59724 t _59725) = (term622 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4821029 _110859 R s _59724 t _59725) (@lem4821071 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821083 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : (term612 _110859 t s R _59724 _59725) = (term622 _110859 R s _59724 t _59725).
Proof. exact (TRANS (@lem4821024 _110859 R s _59724 t _59725) (@lem4821082 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821084 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : ((term468 _110859 t s R _59724 _59725) = (term612 _110859 t s R _59724 _59725)) = ((term622 _110859 R s _59724 t _59725) = (term622 _110859 R s _59724 t _59725)).
Proof. exact (MK_COMB (@lem4820902 _110859 R s _59724 t _59725) (@lem4821083 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821086 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4821087 (x : Prop) : (x = x) = True.
Proof. exact (@lem4821086 Prop x). Qed.
Lemma lem4821088 {_110859 : Type'} (R : type1402 _110859) (s : _110859 -> Prop) (_59724 : _110859) (t : _110859 -> Prop) (_59725 : _110859) : ((term622 _110859 R s _59724 t _59725) = (term622 _110859 R s _59724 t _59725)) = True.
Proof. exact (@lem4821087 (term622 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821089 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : ((term468 _110859 t s R _59724 _59725) = (term612 _110859 t s R _59724 _59725)) = True.
Proof. exact (TRANS (@lem4821084 _110859 R s _59724 t _59725) (@lem4821088 _110859 R s _59724 t _59725)). Qed.
Lemma lem4821090 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : True = ((term468 _110859 t s R _59724 _59725) = (term612 _110859 t s R _59724 _59725)).
Proof. exact (SYM (@lem4821089 _110859 t s R _59724 _59725)). Qed.
Lemma lem4821091 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term468 _110859 t s R _59724 _59725) = (term612 _110859 t s R _59724 _59725).
Proof. exact (EQ_MP (@lem4821090 _110859 t s R _59724 _59725) (@lem0)). Qed.
Lemma lem4821092 {_110859 : Type'} (_59724 : _110859) (_59725 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term612 _110859 t s R _59724 _59725.
Proof. exact (EQ_MP (@lem4821091 _110859 t s R _59724 _59725) (@lem4817604 _110859 _59724 _59725 x y t s R h1)). Qed.
Lemma lem4821094 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4821095 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59725 : _110859) (t : _110859 -> Prop) (_59724 : _110859) : (term612 _110859 t s R _59724 _59725) = (term625 _110859 s R _59725 t _59724).
Proof. exact (@lem4821094 (term616 _110859 t s R _59724 _59725) (t _59724)). Qed.
Lemma lem4821097 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4821098 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term626 _110859 t s R _59724 _59725) = (term627 _110859 t s R _59724 _59725).
Proof. exact (@lem4821097 (term79 _110859 s _59724) (term466 _110859 t s R _59724 _59725)). Qed.
Lemma lem4821100 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4821101 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) : (term183 _110859 s _59724) = (s _59724).
Proof. exact (@lem4821100 (s _59724)). Qed.
Lemma lem4821102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4821103 {_110859 : Type'} (s : _110859 -> Prop) (_59724 : _110859) : (term500 _110859 s _59724) = (term59 _110859 s _59724).
Proof. exact (MK_COMB (@lem4821102) (@lem4821101 _110859 s _59724)). Qed.
Lemma lem4821105 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4821106 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term628 _110859 t s R _59724 _59725) = (term629 _110859 t s R _59724 _59725).
Proof. exact (@lem4821105 (term79 _110859 t _59725) (term630 _110859 s R _59724 _59725)). Qed.
Lemma lem4821108 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4821109 {_110859 : Type'} (t : _110859 -> Prop) (_59725 : _110859) : (term183 _110859 t _59725) = (t _59725).
Proof. exact (@lem4821108 (t _59725)). Qed.
Lemma lem4821110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4821111 {_110859 : Type'} (t : _110859 -> Prop) (_59725 : _110859) : (term500 _110859 t _59725) = (term59 _110859 t _59725).
Proof. exact (MK_COMB (@lem4821110) (@lem4821109 _110859 t _59725)). Qed.
Lemma lem4821113 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4821114 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term631 _110859 s R _59724 _59725) = (term632 _110859 s R _59724 _59725).
Proof. exact (@lem4821113 (s _59725) (R _59724 _59725)). Qed.
Lemma lem4821115 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term629 _110859 t s R _59724 _59725) = (term633 _110859 t s R _59724 _59725).
Proof. exact (MK_COMB (@lem4821111 _110859 t _59725) (@lem4821114 _110859 s R _59724 _59725)). Qed.
Lemma lem4821116 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term628 _110859 t s R _59724 _59725) = (term633 _110859 t s R _59724 _59725).
Proof. exact (TRANS (@lem4821106 _110859 t s R _59724 _59725) (@lem4821115 _110859 t s R _59724 _59725)). Qed.
Lemma lem4821117 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term627 _110859 t s R _59724 _59725) = (term634 _110859 t s R _59724 _59725).
Proof. exact (MK_COMB (@lem4821103 _110859 s _59724) (@lem4821116 _110859 t s R _59724 _59725)). Qed.
Lemma lem4821118 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term626 _110859 t s R _59724 _59725) = (term634 _110859 t s R _59724 _59725).
Proof. exact (TRANS (@lem4821098 _110859 t s R _59724 _59725) (@lem4821117 _110859 t s R _59724 _59725)). Qed.
Lemma lem4821119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4821120 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (_59724 : _110859) (_59725 : _110859) : (term635 _110859 t s R _59724 _59725) = (term636 _110859 t s R _59724 _59725).
Proof. exact (MK_COMB (@lem4821119) (@lem4821118 _110859 t s R _59724 _59725)). Qed.
Lemma lem4821121 {_110859 : Type'} (t : _110859 -> Prop) (_59724 : _110859) : (t _59724) = (t _59724).
Proof. exact (eq_refl (t _59724)). Qed.
Lemma lem4821122 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59725 : _110859) (t : _110859 -> Prop) (_59724 : _110859) : (term625 _110859 s R _59725 t _59724) = (term637 _110859 s R _59725 t _59724).
Proof. exact (MK_COMB (@lem4821120 _110859 t s R _59724 _59725) (@lem4821121 _110859 t _59724)). Qed.
Lemma lem4821123 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) (_59725 : _110859) (t : _110859 -> Prop) (_59724 : _110859) : (term612 _110859 t s R _59724 _59725) = (term637 _110859 s R _59725 t _59724).
Proof. exact (TRANS (@lem4821095 _110859 s R _59725 t _59724) (@lem4821122 _110859 s R _59725 t _59724)). Qed.
Lemma lem4821125 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : term368 _110859 x y t s R) : term632 _110859 s R x y.
Proof. exact (conj (@lem4820704 _110859 x y t s R h1 h2 h3) (@lem4820711 _110859 x y t s R h3)). Qed.
Lemma lem4821126 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : t y) (h4 : term368 _110859 x y t s R) : term633 _110859 t s R x y.
Proof. exact (conj (@lem4820395 _110859 t y h3) (@lem4821125 _110859 x y t s R h1 h2 h4)). Qed.
Lemma lem4821127 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : t y) (h4 : term368 _110859 x y t s R) : term634 _110859 t s R x y.
Proof. exact (conj (@lem4820388 _110859 s x h2) (@lem4821126 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4821129 {_110859 : Type'} (_59725 : _110859) (_59724 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term637 _110859 s R _59725 t _59724.
Proof. exact (EQ_MP (@lem4821123 _110859 s R _59725 t _59724) (@lem4821092 _110859 _59724 _59725 x y t s R h1)). Qed.
Lemma lem4821130 {_110859 : Type'} (_59725 : _110859) (_59724 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term637 _110859 s R _59725 t _59724.
Proof. exact (@lem4821129 _110859 _59725 _59724 x y t s R h1). Qed.
Lemma lem4821131 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term637 _110859 s R y t x.
Proof. exact (@lem4821130 _110859 y x x y t s R h1). Qed.
Lemma lem4821134 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : t y) (h4 : term368 _110859 x y t s R) : t x.
Proof. exact (@lem4821131 _110859 x y t s R h4 (@lem4821127 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4821135 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : t y) (h4 : term368 _110859 x y t s R) : term469 _110859 t x.
Proof. exact (fun h0 : term79 _110859 t x => @lem4821134 _110859 x y t s R h1 h2 h3 h4). Qed.
Lemma lem4821137 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821138 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term469 _110859 t x) = (t x).
Proof. exact (@lem4821137 (t x)). Qed.
Lemma lem4821139 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : t y) (h4 : term368 _110859 x y t s R) : t x.
Proof. exact (EQ_MP (@lem4821138 _110859 t x) (@lem4821135 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4821141 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (h1). Qed.
Lemma lem4821142 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4821141 _110859 t y h1). Qed.
Lemma lem4821144 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821145 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4821144 (t y)). Qed.
Lemma lem4821146 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (EQ_MP (@lem4821145 _110859 t y) (@lem4821142 _110859 t y h1)). Qed.
Lemma lem4821148 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4821149 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4821148 _110859 x y t s R h1). Qed.
Lemma lem4821151 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4821152 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4821151 (R x y)). Qed.
Lemma lem4821153 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4821152 _110859 R x y) (@lem4821149 _110859 x y t s R h1)). Qed.
Lemma lem4821169 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821170 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term455 _110859 t R _59722 _59723) = (term473 _110859 t R _59722 _59723).
Proof. exact (@lem4821169 (_59722 = _59723) (term79 _110859 t _59723) (R _59722 _59723)). Qed.
Lemma lem4821186 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4821187 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term474 _110859 t R _59722 _59723) = (term475 _110859 R _59722 t _59723).
Proof. exact (@lem4821186 (R _59722 _59723) (term79 _110859 t _59723)). Qed.
Lemma lem4821193 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) : (term476 _110859 _59722 _59723) = (term476 _110859 _59722 _59723).
Proof. exact (eq_refl (term476 _110859 _59722 _59723)). Qed.
Lemma lem4821194 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term473 _110859 t R _59722 _59723) = (term477 _110859 R _59722 t _59723).
Proof. exact (MK_COMB (@lem4821193 _110859 _59722 _59723) (@lem4821187 _110859 R _59722 t _59723)). Qed.
Lemma lem4821198 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821199 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term477 _110859 R _59722 t _59723) = (term478 _110859 R _59722 t _59723).
Proof. exact (@lem4821198 (R _59722 _59723) (_59722 = _59723) (term79 _110859 t _59723)). Qed.
Lemma lem4821217 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term473 _110859 t R _59722 _59723) = (term478 _110859 R _59722 t _59723).
Proof. exact (TRANS (@lem4821194 _110859 R _59722 t _59723) (@lem4821199 _110859 R _59722 t _59723)). Qed.
Lemma lem4821218 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term455 _110859 t R _59722 _59723) = (term478 _110859 R _59722 t _59723).
Proof. exact (TRANS (@lem4821170 _110859 t R _59722 _59723) (@lem4821217 _110859 R _59722 t _59723)). Qed.
Lemma lem4821219 {_110859 : Type'} (t : _110859 -> Prop) (_59722 : _110859) : (term152 _110859 t _59722) = (term152 _110859 t _59722).
Proof. exact (eq_refl (term152 _110859 t _59722)). Qed.
Lemma lem4821220 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term456 _110859 t R _59722 _59723) = (term479 _110859 R _59722 t _59723).
Proof. exact (MK_COMB (@lem4821219 _110859 t _59722) (@lem4821218 _110859 R _59722 t _59723)). Qed.
Lemma lem4821224 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821225 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term479 _110859 R _59722 t _59723) = (term480 _110859 R _59722 t _59723).
Proof. exact (@lem4821224 (R _59722 _59723) (term79 _110859 t _59722) (term481 _110859 _59722 t _59723)). Qed.
Lemma lem4821239 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821240 {_110859 : Type'} (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term482 _110859 _59722 t _59723) = (term483 _110859 _59722 t _59723).
Proof. exact (@lem4821239 (_59722 = _59723) (term79 _110859 t _59722) (term79 _110859 t _59723)). Qed.
Lemma lem4821258 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term484 _110859 R _59722 _59723) = (term484 _110859 R _59722 _59723).
Proof. exact (eq_refl (term484 _110859 R _59722 _59723)). Qed.
Lemma lem4821259 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term480 _110859 R _59722 t _59723) = (term485 _110859 R _59722 t _59723).
Proof. exact (MK_COMB (@lem4821258 _110859 R _59722 _59723) (@lem4821240 _110859 _59722 t _59723)). Qed.
Lemma lem4821270 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term479 _110859 R _59722 t _59723) = (term485 _110859 R _59722 t _59723).
Proof. exact (TRANS (@lem4821225 _110859 R _59722 t _59723) (@lem4821259 _110859 R _59722 t _59723)). Qed.
Lemma lem4821271 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term456 _110859 t R _59722 _59723) = (term485 _110859 R _59722 t _59723).
Proof. exact (TRANS (@lem4821220 _110859 R _59722 t _59723) (@lem4821270 _110859 R _59722 t _59723)). Qed.
Lemma lem4821272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4821273 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term486 _110859 t R _59722 _59723) = (term487 _110859 R _59722 t _59723).
Proof. exact (MK_COMB (@lem4821272) (@lem4821271 _110859 R _59722 t _59723)). Qed.
Lemma lem4821299 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4821300 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term474 _110859 t R _59722 _59723) = (term475 _110859 R _59722 t _59723).
Proof. exact (@lem4821299 (R _59722 _59723) (term79 _110859 t _59723)). Qed.
Lemma lem4821306 {_110859 : Type'} (t : _110859 -> Prop) (_59722 : _110859) : (term152 _110859 t _59722) = (term152 _110859 t _59722).
Proof. exact (eq_refl (term152 _110859 t _59722)). Qed.
Lemma lem4821307 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term488 _110859 t R _59722 _59723) = (term489 _110859 R _59722 t _59723).
Proof. exact (MK_COMB (@lem4821306 _110859 t _59722) (@lem4821300 _110859 R _59722 t _59723)). Qed.
Lemma lem4821311 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821312 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term489 _110859 R _59722 t _59723) = (term490 _110859 R _59722 t _59723).
Proof. exact (@lem4821311 (R _59722 _59723) (term79 _110859 t _59722) (term79 _110859 t _59723)). Qed.
Lemma lem4821328 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term488 _110859 t R _59722 _59723) = (term490 _110859 R _59722 t _59723).
Proof. exact (TRANS (@lem4821307 _110859 R _59722 t _59723) (@lem4821312 _110859 R _59722 t _59723)). Qed.
Lemma lem4821329 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) : (term476 _110859 _59722 _59723) = (term476 _110859 _59722 _59723).
Proof. exact (eq_refl (term476 _110859 _59722 _59723)). Qed.
Lemma lem4821330 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term491 _110859 t R _59722 _59723) = (term492 _110859 R _59722 t _59723).
Proof. exact (MK_COMB (@lem4821329 _110859 _59722 _59723) (@lem4821328 _110859 R _59722 t _59723)). Qed.
Lemma lem4821334 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821335 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term492 _110859 R _59722 t _59723) = (term485 _110859 R _59722 t _59723).
Proof. exact (@lem4821334 (R _59722 _59723) (_59722 = _59723) (term493 _110859 _59722 t _59723)). Qed.
Lemma lem4821363 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : (term491 _110859 t R _59722 _59723) = (term485 _110859 R _59722 t _59723).
Proof. exact (TRANS (@lem4821330 _110859 R _59722 t _59723) (@lem4821335 _110859 R _59722 t _59723)). Qed.
Lemma lem4821364 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : ((term456 _110859 t R _59722 _59723) = (term491 _110859 t R _59722 _59723)) = ((term485 _110859 R _59722 t _59723) = (term485 _110859 R _59722 t _59723)).
Proof. exact (MK_COMB (@lem4821273 _110859 R _59722 t _59723) (@lem4821363 _110859 R _59722 t _59723)). Qed.
Lemma lem4821366 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4821367 (x : Prop) : (x = x) = True.
Proof. exact (@lem4821366 Prop x). Qed.
Lemma lem4821368 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (t : _110859 -> Prop) (_59723 : _110859) : ((term485 _110859 R _59722 t _59723) = (term485 _110859 R _59722 t _59723)) = True.
Proof. exact (@lem4821367 (term485 _110859 R _59722 t _59723)). Qed.
Lemma lem4821369 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : ((term456 _110859 t R _59722 _59723) = (term491 _110859 t R _59722 _59723)) = True.
Proof. exact (TRANS (@lem4821364 _110859 R _59722 t _59723) (@lem4821368 _110859 R _59722 t _59723)). Qed.
Lemma lem4821370 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : True = ((term456 _110859 t R _59722 _59723) = (term491 _110859 t R _59722 _59723)).
Proof. exact (SYM (@lem4821369 _110859 t R _59722 _59723)). Qed.
Lemma lem4821371 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term456 _110859 t R _59722 _59723) = (term491 _110859 t R _59722 _59723).
Proof. exact (EQ_MP (@lem4821370 _110859 t R _59722 _59723) (@lem0)). Qed.
Lemma lem4821372 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term491 _110859 t R _59722 _59723.
Proof. exact (EQ_MP (@lem4821371 _110859 t R _59722 _59723) (@lem4817572 _110859 _59722 _59723 x y t s R h1)). Qed.
Lemma lem4821374 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4821375 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term491 _110859 t R _59722 _59723) = (term495 _110859 t R _59722 _59723).
Proof. exact (@lem4821374 (term488 _110859 t R _59722 _59723) (_59722 = _59723)). Qed.
Lemma lem4821377 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4821378 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term498 _110859 t R _59722 _59723) = (term499 _110859 t R _59722 _59723).
Proof. exact (@lem4821377 (term79 _110859 t _59722) (term474 _110859 t R _59722 _59723)). Qed.
Lemma lem4821380 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4821381 {_110859 : Type'} (t : _110859 -> Prop) (_59722 : _110859) : (term183 _110859 t _59722) = (t _59722).
Proof. exact (@lem4821380 (t _59722)). Qed.
Lemma lem4821382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4821383 {_110859 : Type'} (t : _110859 -> Prop) (_59722 : _110859) : (term500 _110859 t _59722) = (term59 _110859 t _59722).
Proof. exact (MK_COMB (@lem4821382) (@lem4821381 _110859 t _59722)). Qed.
Lemma lem4821385 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4821386 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term501 _110859 t R _59722 _59723) = (term502 _110859 t R _59722 _59723).
Proof. exact (@lem4821385 (term79 _110859 t _59723) (R _59722 _59723)). Qed.
Lemma lem4821388 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4821389 {_110859 : Type'} (t : _110859 -> Prop) (_59723 : _110859) : (term183 _110859 t _59723) = (t _59723).
Proof. exact (@lem4821388 (t _59723)). Qed.
Lemma lem4821390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4821391 {_110859 : Type'} (t : _110859 -> Prop) (_59723 : _110859) : (term500 _110859 t _59723) = (term59 _110859 t _59723).
Proof. exact (MK_COMB (@lem4821390) (@lem4821389 _110859 t _59723)). Qed.
Lemma lem4821392 {_110859 : Type'} (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term438 _110859 R _59722 _59723) = (term438 _110859 R _59722 _59723).
Proof. exact (eq_refl (term438 _110859 R _59722 _59723)). Qed.
Lemma lem4821393 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term502 _110859 t R _59722 _59723) = (term503 _110859 t R _59722 _59723).
Proof. exact (MK_COMB (@lem4821391 _110859 t _59723) (@lem4821392 _110859 R _59722 _59723)). Qed.
Lemma lem4821394 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term501 _110859 t R _59722 _59723) = (term503 _110859 t R _59722 _59723).
Proof. exact (TRANS (@lem4821386 _110859 t R _59722 _59723) (@lem4821393 _110859 t R _59722 _59723)). Qed.
Lemma lem4821395 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term499 _110859 t R _59722 _59723) = (term504 _110859 t R _59722 _59723).
Proof. exact (MK_COMB (@lem4821383 _110859 t _59722) (@lem4821394 _110859 t R _59722 _59723)). Qed.
Lemma lem4821396 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term498 _110859 t R _59722 _59723) = (term504 _110859 t R _59722 _59723).
Proof. exact (TRANS (@lem4821378 _110859 t R _59722 _59723) (@lem4821395 _110859 t R _59722 _59723)). Qed.
Lemma lem4821397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4821398 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term505 _110859 t R _59722 _59723) = (term506 _110859 t R _59722 _59723).
Proof. exact (MK_COMB (@lem4821397) (@lem4821396 _110859 t R _59722 _59723)). Qed.
Lemma lem4821399 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) : (_59722 = _59723) = (_59722 = _59723).
Proof. exact (eq_refl (_59722 = _59723)). Qed.
Lemma lem4821400 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term495 _110859 t R _59722 _59723) = (term507 _110859 t R _59722 _59723).
Proof. exact (MK_COMB (@lem4821398 _110859 t R _59722 _59723) (@lem4821399 _110859 _59722 _59723)). Qed.
Lemma lem4821401 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59722 : _110859) (_59723 : _110859) : (term491 _110859 t R _59722 _59723) = (term507 _110859 t R _59722 _59723).
Proof. exact (TRANS (@lem4821375 _110859 t R _59722 _59723) (@lem4821400 _110859 t R _59722 _59723)). Qed.
Lemma lem4821403 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t y) (h2 : term368 _110859 x y t s R) : term503 _110859 t R x y.
Proof. exact (conj (@lem4821146 _110859 t y h1) (@lem4821153 _110859 x y t s R h2)). Qed.
Lemma lem4821404 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : t y) (h4 : term368 _110859 x y t s R) : term504 _110859 t R x y.
Proof. exact (conj (@lem4821139 _110859 x y t s R h1 h2 h3 h4) (@lem4821403 _110859 x y t s R h3 h4)). Qed.
Lemma lem4821406 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R _59722 _59723.
Proof. exact (EQ_MP (@lem4821401 _110859 t R _59722 _59723) (@lem4821372 _110859 _59722 _59723 x y t s R h1)). Qed.
Lemma lem4821407 {_110859 : Type'} (_59722 : _110859) (_59723 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R _59722 _59723.
Proof. exact (@lem4821406 _110859 _59722 _59723 x y t s R h1). Qed.
Lemma lem4821408 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R x y.
Proof. exact (@lem4821407 _110859 x y x y t s R h1). Qed.
Lemma lem4821411 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term41 _110859 x y) (h2 : s x) (h3 : t y) (h4 : term368 _110859 x y t s R) : x = y.
Proof. exact (@lem4821408 _110859 x y t s R h4 (@lem4821404 _110859 x y t s R h1 h2 h3 h4)). Qed.
Lemma lem4821412 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : term508 _110859 x y.
Proof. exact (fun h0 : term41 _110859 x y => @lem4821411 _110859 x y t s R h0 h1 h2 h3). Qed.
Lemma lem4821414 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821415 {_110859 : Type'} (x : _110859) (y : _110859) : (term508 _110859 x y) = (x = y).
Proof. exact (@lem4821414 (x = y)). Qed.
Lemma lem4821416 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : x = y.
Proof. exact (EQ_MP (@lem4821415 _110859 x y) (@lem4821412 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4821419 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4821421 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term509 _110859 x y).
Proof. exact (@lem4821419 (x = y)). Qed.
Lemma lem4821424 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term509 _110859 x y.
Proof. exact (EQ_MP (@lem4821421 _110859 x y) (@lem4817576 _110859 x y t s R h1)). Qed.
Lemma lem4821427 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (@lem4821424 _110859 x y t s R h3 (@lem4821416 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4821428 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : term510.
Proof. exact (fun h0 : ~ False => @lem4821427 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4821430 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821431 : term510 = False.
Proof. exact (@lem4821430 False). Qed.
Lemma lem4821432 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821431) (@lem4821428 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4821479 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem4821480 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : term469 _110859 t x.
Proof. exact (fun h0 : term79 _110859 t x => @lem4821479 _110859 t x h1). Qed.
Lemma lem4821482 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821483 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) : (term469 _110859 t x) = (t x).
Proof. exact (@lem4821482 (t x)). Qed.
Lemma lem4821484 {_110859 : Type'} (t : _110859 -> Prop) (x : _110859) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem4821483 _110859 t x) (@lem4821480 _110859 t x h1)). Qed.
Lemma lem4821486 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (h1). Qed.
Lemma lem4821487 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : term469 _110859 t y.
Proof. exact (fun h0 : term79 _110859 t y => @lem4821486 _110859 t y h1). Qed.
Lemma lem4821489 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821490 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) : (term469 _110859 t y) = (t y).
Proof. exact (@lem4821489 (t y)). Qed.
Lemma lem4821491 {_110859 : Type'} (t : _110859 -> Prop) (y : _110859) (h1 : t y) : t y.
Proof. exact (EQ_MP (@lem4821490 _110859 t y) (@lem4821487 _110859 t y h1)). Qed.
Lemma lem4821493 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (proj2 (@lem4816036 _110859 x y t s R h1)). Qed.
Lemma lem4821494 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term471 _110859 R x y.
Proof. exact (fun h0 : R x y => @lem4821493 _110859 x y t s R h1). Qed.
Lemma lem4821496 (p : Prop) : (term472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4821497 {_110859 : Type'} (R : type1402 _110859) (x : _110859) (y : _110859) : (term471 _110859 R x y) = (term438 _110859 R x y).
Proof. exact (@lem4821496 (R x y)). Qed.
Lemma lem4821498 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term438 _110859 R x y.
Proof. exact (EQ_MP (@lem4821497 _110859 R x y) (@lem4821494 _110859 x y t s R h1)). Qed.
Lemma lem4821514 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821515 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term455 _110859 t R _59728 _59729) = (term473 _110859 t R _59728 _59729).
Proof. exact (@lem4821514 (_59728 = _59729) (term79 _110859 t _59729) (R _59728 _59729)). Qed.
Lemma lem4821531 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4821532 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term474 _110859 t R _59728 _59729) = (term475 _110859 R _59728 t _59729).
Proof. exact (@lem4821531 (R _59728 _59729) (term79 _110859 t _59729)). Qed.
Lemma lem4821538 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) : (term476 _110859 _59728 _59729) = (term476 _110859 _59728 _59729).
Proof. exact (eq_refl (term476 _110859 _59728 _59729)). Qed.
Lemma lem4821539 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term473 _110859 t R _59728 _59729) = (term477 _110859 R _59728 t _59729).
Proof. exact (MK_COMB (@lem4821538 _110859 _59728 _59729) (@lem4821532 _110859 R _59728 t _59729)). Qed.
Lemma lem4821543 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821544 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term477 _110859 R _59728 t _59729) = (term478 _110859 R _59728 t _59729).
Proof. exact (@lem4821543 (R _59728 _59729) (_59728 = _59729) (term79 _110859 t _59729)). Qed.
Lemma lem4821562 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term473 _110859 t R _59728 _59729) = (term478 _110859 R _59728 t _59729).
Proof. exact (TRANS (@lem4821539 _110859 R _59728 t _59729) (@lem4821544 _110859 R _59728 t _59729)). Qed.
Lemma lem4821563 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term455 _110859 t R _59728 _59729) = (term478 _110859 R _59728 t _59729).
Proof. exact (TRANS (@lem4821515 _110859 t R _59728 _59729) (@lem4821562 _110859 R _59728 t _59729)). Qed.
Lemma lem4821564 {_110859 : Type'} (t : _110859 -> Prop) (_59728 : _110859) : (term152 _110859 t _59728) = (term152 _110859 t _59728).
Proof. exact (eq_refl (term152 _110859 t _59728)). Qed.
Lemma lem4821565 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term456 _110859 t R _59728 _59729) = (term479 _110859 R _59728 t _59729).
Proof. exact (MK_COMB (@lem4821564 _110859 t _59728) (@lem4821563 _110859 R _59728 t _59729)). Qed.
Lemma lem4821569 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821570 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term479 _110859 R _59728 t _59729) = (term480 _110859 R _59728 t _59729).
Proof. exact (@lem4821569 (R _59728 _59729) (term79 _110859 t _59728) (term481 _110859 _59728 t _59729)). Qed.
Lemma lem4821584 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821585 {_110859 : Type'} (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term482 _110859 _59728 t _59729) = (term483 _110859 _59728 t _59729).
Proof. exact (@lem4821584 (_59728 = _59729) (term79 _110859 t _59728) (term79 _110859 t _59729)). Qed.
Lemma lem4821603 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term484 _110859 R _59728 _59729) = (term484 _110859 R _59728 _59729).
Proof. exact (eq_refl (term484 _110859 R _59728 _59729)). Qed.
Lemma lem4821604 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term480 _110859 R _59728 t _59729) = (term485 _110859 R _59728 t _59729).
Proof. exact (MK_COMB (@lem4821603 _110859 R _59728 _59729) (@lem4821585 _110859 _59728 t _59729)). Qed.
Lemma lem4821615 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term479 _110859 R _59728 t _59729) = (term485 _110859 R _59728 t _59729).
Proof. exact (TRANS (@lem4821570 _110859 R _59728 t _59729) (@lem4821604 _110859 R _59728 t _59729)). Qed.
Lemma lem4821616 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term456 _110859 t R _59728 _59729) = (term485 _110859 R _59728 t _59729).
Proof. exact (TRANS (@lem4821565 _110859 R _59728 t _59729) (@lem4821615 _110859 R _59728 t _59729)). Qed.
Lemma lem4821617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4821618 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term486 _110859 t R _59728 _59729) = (term487 _110859 R _59728 t _59729).
Proof. exact (MK_COMB (@lem4821617) (@lem4821616 _110859 R _59728 t _59729)). Qed.
Lemma lem4821644 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4821645 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term474 _110859 t R _59728 _59729) = (term475 _110859 R _59728 t _59729).
Proof. exact (@lem4821644 (R _59728 _59729) (term79 _110859 t _59729)). Qed.
Lemma lem4821651 {_110859 : Type'} (t : _110859 -> Prop) (_59728 : _110859) : (term152 _110859 t _59728) = (term152 _110859 t _59728).
Proof. exact (eq_refl (term152 _110859 t _59728)). Qed.
Lemma lem4821652 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term488 _110859 t R _59728 _59729) = (term489 _110859 R _59728 t _59729).
Proof. exact (MK_COMB (@lem4821651 _110859 t _59728) (@lem4821645 _110859 R _59728 t _59729)). Qed.
Lemma lem4821656 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821657 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term489 _110859 R _59728 t _59729) = (term490 _110859 R _59728 t _59729).
Proof. exact (@lem4821656 (R _59728 _59729) (term79 _110859 t _59728) (term79 _110859 t _59729)). Qed.
Lemma lem4821673 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term488 _110859 t R _59728 _59729) = (term490 _110859 R _59728 t _59729).
Proof. exact (TRANS (@lem4821652 _110859 R _59728 t _59729) (@lem4821657 _110859 R _59728 t _59729)). Qed.
Lemma lem4821674 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) : (term476 _110859 _59728 _59729) = (term476 _110859 _59728 _59729).
Proof. exact (eq_refl (term476 _110859 _59728 _59729)). Qed.
Lemma lem4821675 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term491 _110859 t R _59728 _59729) = (term492 _110859 R _59728 t _59729).
Proof. exact (MK_COMB (@lem4821674 _110859 _59728 _59729) (@lem4821673 _110859 R _59728 t _59729)). Qed.
Lemma lem4821679 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4821680 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term492 _110859 R _59728 t _59729) = (term485 _110859 R _59728 t _59729).
Proof. exact (@lem4821679 (R _59728 _59729) (_59728 = _59729) (term493 _110859 _59728 t _59729)). Qed.
Lemma lem4821708 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : (term491 _110859 t R _59728 _59729) = (term485 _110859 R _59728 t _59729).
Proof. exact (TRANS (@lem4821675 _110859 R _59728 t _59729) (@lem4821680 _110859 R _59728 t _59729)). Qed.
Lemma lem4821709 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : ((term456 _110859 t R _59728 _59729) = (term491 _110859 t R _59728 _59729)) = ((term485 _110859 R _59728 t _59729) = (term485 _110859 R _59728 t _59729)).
Proof. exact (MK_COMB (@lem4821618 _110859 R _59728 t _59729) (@lem4821708 _110859 R _59728 t _59729)). Qed.
Lemma lem4821711 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4821712 (x : Prop) : (x = x) = True.
Proof. exact (@lem4821711 Prop x). Qed.
Lemma lem4821713 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (t : _110859 -> Prop) (_59729 : _110859) : ((term485 _110859 R _59728 t _59729) = (term485 _110859 R _59728 t _59729)) = True.
Proof. exact (@lem4821712 (term485 _110859 R _59728 t _59729)). Qed.
Lemma lem4821714 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : ((term456 _110859 t R _59728 _59729) = (term491 _110859 t R _59728 _59729)) = True.
Proof. exact (TRANS (@lem4821709 _110859 R _59728 t _59729) (@lem4821713 _110859 R _59728 t _59729)). Qed.
Lemma lem4821715 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : True = ((term456 _110859 t R _59728 _59729) = (term491 _110859 t R _59728 _59729)).
Proof. exact (SYM (@lem4821714 _110859 t R _59728 _59729)). Qed.
Lemma lem4821716 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term456 _110859 t R _59728 _59729) = (term491 _110859 t R _59728 _59729).
Proof. exact (EQ_MP (@lem4821715 _110859 t R _59728 _59729) (@lem0)). Qed.
Lemma lem4821717 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term491 _110859 t R _59728 _59729.
Proof. exact (EQ_MP (@lem4821716 _110859 t R _59728 _59729) (@lem4817664 _110859 _59728 _59729 x y t s R h1)). Qed.
Lemma lem4821719 (b : Prop) (a : Prop) : (a \/ b) = (term494 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4821720 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term491 _110859 t R _59728 _59729) = (term495 _110859 t R _59728 _59729).
Proof. exact (@lem4821719 (term488 _110859 t R _59728 _59729) (_59728 = _59729)). Qed.
Lemma lem4821722 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4821723 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term498 _110859 t R _59728 _59729) = (term499 _110859 t R _59728 _59729).
Proof. exact (@lem4821722 (term79 _110859 t _59728) (term474 _110859 t R _59728 _59729)). Qed.
Lemma lem4821725 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4821726 {_110859 : Type'} (t : _110859 -> Prop) (_59728 : _110859) : (term183 _110859 t _59728) = (t _59728).
Proof. exact (@lem4821725 (t _59728)). Qed.
Lemma lem4821727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4821728 {_110859 : Type'} (t : _110859 -> Prop) (_59728 : _110859) : (term500 _110859 t _59728) = (term59 _110859 t _59728).
Proof. exact (MK_COMB (@lem4821727) (@lem4821726 _110859 t _59728)). Qed.
Lemma lem4821730 (a : Prop) (b : Prop) : (term496 a b) = (term497 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4821731 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term501 _110859 t R _59728 _59729) = (term502 _110859 t R _59728 _59729).
Proof. exact (@lem4821730 (term79 _110859 t _59729) (R _59728 _59729)). Qed.
Lemma lem4821733 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4821734 {_110859 : Type'} (t : _110859 -> Prop) (_59729 : _110859) : (term183 _110859 t _59729) = (t _59729).
Proof. exact (@lem4821733 (t _59729)). Qed.
Lemma lem4821735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4821736 {_110859 : Type'} (t : _110859 -> Prop) (_59729 : _110859) : (term500 _110859 t _59729) = (term59 _110859 t _59729).
Proof. exact (MK_COMB (@lem4821735) (@lem4821734 _110859 t _59729)). Qed.
Lemma lem4821737 {_110859 : Type'} (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term438 _110859 R _59728 _59729) = (term438 _110859 R _59728 _59729).
Proof. exact (eq_refl (term438 _110859 R _59728 _59729)). Qed.
Lemma lem4821738 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term502 _110859 t R _59728 _59729) = (term503 _110859 t R _59728 _59729).
Proof. exact (MK_COMB (@lem4821736 _110859 t _59729) (@lem4821737 _110859 R _59728 _59729)). Qed.
Lemma lem4821739 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term501 _110859 t R _59728 _59729) = (term503 _110859 t R _59728 _59729).
Proof. exact (TRANS (@lem4821731 _110859 t R _59728 _59729) (@lem4821738 _110859 t R _59728 _59729)). Qed.
Lemma lem4821740 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term499 _110859 t R _59728 _59729) = (term504 _110859 t R _59728 _59729).
Proof. exact (MK_COMB (@lem4821728 _110859 t _59728) (@lem4821739 _110859 t R _59728 _59729)). Qed.
Lemma lem4821741 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term498 _110859 t R _59728 _59729) = (term504 _110859 t R _59728 _59729).
Proof. exact (TRANS (@lem4821723 _110859 t R _59728 _59729) (@lem4821740 _110859 t R _59728 _59729)). Qed.
Lemma lem4821742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4821743 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term505 _110859 t R _59728 _59729) = (term506 _110859 t R _59728 _59729).
Proof. exact (MK_COMB (@lem4821742) (@lem4821741 _110859 t R _59728 _59729)). Qed.
Lemma lem4821744 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) : (_59728 = _59729) = (_59728 = _59729).
Proof. exact (eq_refl (_59728 = _59729)). Qed.
Lemma lem4821745 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term495 _110859 t R _59728 _59729) = (term507 _110859 t R _59728 _59729).
Proof. exact (MK_COMB (@lem4821743 _110859 t R _59728 _59729) (@lem4821744 _110859 _59728 _59729)). Qed.
Lemma lem4821746 {_110859 : Type'} (t : _110859 -> Prop) (R : type1402 _110859) (_59728 : _110859) (_59729 : _110859) : (term491 _110859 t R _59728 _59729) = (term507 _110859 t R _59728 _59729).
Proof. exact (TRANS (@lem4821720 _110859 t R _59728 _59729) (@lem4821745 _110859 t R _59728 _59729)). Qed.
Lemma lem4821748 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t y) (h2 : term368 _110859 x y t s R) : term503 _110859 t R x y.
Proof. exact (conj (@lem4821491 _110859 t y h1) (@lem4821498 _110859 x y t s R h2)). Qed.
Lemma lem4821749 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : term504 _110859 t R x y.
Proof. exact (conj (@lem4821484 _110859 t x h1) (@lem4821748 _110859 x y t s R h2 h3)). Qed.
Lemma lem4821751 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R _59728 _59729.
Proof. exact (EQ_MP (@lem4821746 _110859 t R _59728 _59729) (@lem4821717 _110859 _59728 _59729 x y t s R h1)). Qed.
Lemma lem4821752 {_110859 : Type'} (_59728 : _110859) (_59729 : _110859) (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R _59728 _59729.
Proof. exact (@lem4821751 _110859 _59728 _59729 x y t s R h1). Qed.
Lemma lem4821753 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term507 _110859 t R x y.
Proof. exact (@lem4821752 _110859 x y x y t s R h1). Qed.
Lemma lem4821756 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : x = y.
Proof. exact (@lem4821753 _110859 x y t s R h3 (@lem4821749 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4821757 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : term508 _110859 x y.
Proof. exact (fun h0 : term41 _110859 x y => @lem4821756 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4821759 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821760 {_110859 : Type'} (x : _110859) (y : _110859) : (term508 _110859 x y) = (x = y).
Proof. exact (@lem4821759 (x = y)). Qed.
Lemma lem4821761 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : x = y.
Proof. exact (EQ_MP (@lem4821760 _110859 x y) (@lem4821757 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4821764 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4821766 {_110859 : Type'} (x : _110859) (y : _110859) : (term41 _110859 x y) = (term509 _110859 x y).
Proof. exact (@lem4821764 (x = y)). Qed.
Lemma lem4821769 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : term509 _110859 x y.
Proof. exact (EQ_MP (@lem4821766 _110859 x y) (@lem4817668 _110859 x y t s R h1)). Qed.
Lemma lem4821772 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (@lem4821769 _110859 x y t s R h3 (@lem4821761 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4821773 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : term510.
Proof. exact (fun h0 : ~ False => @lem4821772 _110859 x y t s R h1 h2 h3). Qed.
Lemma lem4821775 (p : Prop) : (term470 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4821776 : term510 = False.
Proof. exact (@lem4821775 False). Qed.
Lemma lem4821777 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821776) (@lem4821773 _110859 x y t s R h1 h2 h3)). Qed.
Lemma lem4821778 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4821777 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817672 _110859 t x h1)). Qed.
Lemma lem4821779 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821778 _110859 x y t s R h1 h2 h3) (@lem4817672 _110859 t x h1)). Qed.
Lemma lem4821780 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t y) = False.
Proof. exact (prop_ext (fun h4 : t y => @lem4821779 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817670 _110859 t y h2)). Qed.
Lemma lem4821781 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821780 _110859 x y t s R h1 h2 h3) (@lem4817670 _110859 t y h2)). Qed.
Lemma lem4821782 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4821432 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817580 _110859 s x h1)). Qed.
Lemma lem4821783 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821782 _110859 x y t s R h1 h2 h3) (@lem4817580 _110859 s x h1)). Qed.
Lemma lem4821784 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t y) = False.
Proof. exact (prop_ext (fun h4 : t y => @lem4821783 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817578 _110859 t y h2)). Qed.
Lemma lem4821785 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821784 _110859 x y t s R h1 h2 h3) (@lem4817578 _110859 t y h2)). Qed.
Lemma lem4821786 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4820336 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817488 _110859 t x h2)). Qed.
Lemma lem4821787 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821786 _110859 x y t s R h1 h2 h3) (@lem4817488 _110859 t x h2)). Qed.
Lemma lem4821788 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : (s y) = False.
Proof. exact (prop_ext (fun h4 : s y => @lem4821787 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817486 _110859 s y h1)). Qed.
Lemma lem4821789 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821788 _110859 x y t s R h1 h2 h3) (@lem4817486 _110859 s y h1)). Qed.
Lemma lem4821790 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4819491 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817396 _110859 s x h1)). Qed.
Lemma lem4821791 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821790 _110859 x y t s R h1 h2 h3) (@lem4817396 _110859 s x h1)). Qed.
Lemma lem4821792 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : (s y) = False.
Proof. exact (prop_ext (fun h4 : s y => @lem4821791 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4817394 _110859 s y h2)). Qed.
Lemma lem4821793 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821792 _110859 x y t s R h1 h2 h3) (@lem4817394 _110859 s y h2)). Qed.
Lemma lem4821794 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : (term438 _110859 R y x) = False.
Proof. exact (prop_ext (fun h4 : term438 _110859 R y x => @lem4819146 _110859 t s R y x h1 h2 h3) (fun h4 : False => @lem4817280 _110859 R y x h1)). Qed.
Lemma lem4821795 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4821794 _110859 t s R y x h1 h2 h3) (@lem4817280 _110859 R y x h1)). Qed.
Lemma lem4821796 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : (term438 _110859 R x y) = False.
Proof. exact (prop_ext (fun h4 : term438 _110859 R x y => @lem4818772 _110859 t s R y x h1 h2 h3) (fun h4 : False => @lem4817198 _110859 R x y h1)). Qed.
Lemma lem4821797 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4821796 _110859 t s R y x h1 h2 h3) (@lem4817198 _110859 R x y h1)). Qed.
Lemma lem4821798 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4821781 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816900 _110859 t x h1)). Qed.
Lemma lem4821799 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821798 _110859 x y t s R h1 h2 h3) (@lem4816900 _110859 t x h1)). Qed.
Lemma lem4821800 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t y) = False.
Proof. exact (prop_ext (fun h4 : t y => @lem4821799 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816896 _110859 t y h2)). Qed.
Lemma lem4821801 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821800 _110859 x y t s R h1 h2 h3) (@lem4816896 _110859 t y h2)). Qed.
Lemma lem4821802 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4821785 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816784 _110859 s x h1)). Qed.
Lemma lem4821803 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821802 _110859 x y t s R h1 h2 h3) (@lem4816784 _110859 s x h1)). Qed.
Lemma lem4821804 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t y) = False.
Proof. exact (prop_ext (fun h4 : t y => @lem4821803 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816780 _110859 t y h2)). Qed.
Lemma lem4821805 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821804 _110859 x y t s R h1 h2 h3) (@lem4816780 _110859 t y h2)). Qed.
Lemma lem4821806 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4821789 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816668 _110859 t x h2)). Qed.
Lemma lem4821807 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821806 _110859 x y t s R h1 h2 h3) (@lem4816668 _110859 t x h2)). Qed.
Lemma lem4821808 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : (s y) = False.
Proof. exact (prop_ext (fun h4 : s y => @lem4821807 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816664 _110859 s y h1)). Qed.
Lemma lem4821809 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821808 _110859 x y t s R h1 h2 h3) (@lem4816664 _110859 s y h1)). Qed.
Lemma lem4821810 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4821793 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816552 _110859 s x h1)). Qed.
Lemma lem4821811 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821810 _110859 x y t s R h1 h2 h3) (@lem4816552 _110859 s x h1)). Qed.
Lemma lem4821812 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : (s y) = False.
Proof. exact (prop_ext (fun h4 : s y => @lem4821811 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816548 _110859 s y h2)). Qed.
Lemma lem4821813 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821812 _110859 x y t s R h1 h2 h3) (@lem4816548 _110859 s y h2)). Qed.
Lemma lem4821814 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : (term438 _110859 R y x) = False.
Proof. exact (prop_ext (fun h4 : term438 _110859 R y x => @lem4821795 _110859 t s R y x h1 h2 h3) (fun h4 : False => @lem4816436 _110859 R y x h1)). Qed.
Lemma lem4821815 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4821814 _110859 t s R y x h1 h2 h3) (@lem4816436 _110859 R y x h1)). Qed.
Lemma lem4821816 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : (term438 _110859 R x y) = False.
Proof. exact (prop_ext (fun h4 : term438 _110859 R x y => @lem4821797 _110859 t s R y x h1 h2 h3) (fun h4 : False => @lem4816338 _110859 R x y h1)). Qed.
Lemma lem4821817 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4821816 _110859 t s R y x h1 h2 h3) (@lem4816338 _110859 R x y h1)). Qed.
Lemma lem4821818 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4821801 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816900 _110859 t x h1)). Qed.
Lemma lem4821819 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821818 _110859 x y t s R h1 h2 h3) (@lem4816900 _110859 t x h1)). Qed.
Lemma lem4821820 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t y) = False.
Proof. exact (prop_ext (fun h4 : t y => @lem4821819 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816896 _110859 t y h2)). Qed.
Lemma lem4821821 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821820 _110859 x y t s R h1 h2 h3) (@lem4816896 _110859 t y h2)). Qed.
Lemma lem4821822 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4821805 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816784 _110859 s x h1)). Qed.
Lemma lem4821823 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821822 _110859 x y t s R h1 h2 h3) (@lem4816784 _110859 s x h1)). Qed.
Lemma lem4821824 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : (t y) = False.
Proof. exact (prop_ext (fun h4 : t y => @lem4821823 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816780 _110859 t y h2)). Qed.
Lemma lem4821825 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : t y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821824 _110859 x y t s R h1 h2 h3) (@lem4816780 _110859 t y h2)). Qed.
Lemma lem4821826 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem4821809 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816668 _110859 t x h2)). Qed.
Lemma lem4821827 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821826 _110859 x y t s R h1 h2 h3) (@lem4816668 _110859 t x h2)). Qed.
Lemma lem4821828 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : (s y) = False.
Proof. exact (prop_ext (fun h4 : s y => @lem4821827 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816664 _110859 s y h1)). Qed.
Lemma lem4821829 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : t x) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821828 _110859 x y t s R h1 h2 h3) (@lem4816664 _110859 s y h1)). Qed.
Lemma lem4821830 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem4821813 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816552 _110859 s x h1)). Qed.
Lemma lem4821831 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821830 _110859 x y t s R h1 h2 h3) (@lem4816552 _110859 s x h1)). Qed.
Lemma lem4821832 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : (s y) = False.
Proof. exact (prop_ext (fun h4 : s y => @lem4821831 _110859 x y t s R h1 h2 h3) (fun h4 : False => @lem4816548 _110859 s y h2)). Qed.
Lemma lem4821833 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s x) (h2 : s y) (h3 : term368 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821832 _110859 x y t s R h1 h2 h3) (@lem4816548 _110859 s y h2)). Qed.
Lemma lem4821834 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : (term438 _110859 R y x) = False.
Proof. exact (prop_ext (fun h4 : term438 _110859 R y x => @lem4821815 _110859 t s R y x h1 h2 h3) (fun h4 : False => @lem4816436 _110859 R y x h1)). Qed.
Lemma lem4821835 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R y x) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4821834 _110859 t s R y x h1 h2 h3) (@lem4816436 _110859 R y x h1)). Qed.
Lemma lem4821836 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : (term438 _110859 R x y) = False.
Proof. exact (prop_ext (fun h4 : term438 _110859 R x y => @lem4821817 _110859 t s R y x h1 h2 h3) (fun h4 : False => @lem4816338 _110859 R x y h1)). Qed.
Lemma lem4821837 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term438 _110859 R x y) (h2 : term333 _110859 t s R y x) (h3 : term196 _110859 t s R y x) : False.
Proof. exact (EQ_MP (@lem4821836 _110859 t s R y x h1 h2 h3) (@lem4816338 _110859 R x y h1)). Qed.
Lemma lem4821838 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : t y) (h2 : term368 _110859 x y t s R) : False.
Proof. exact (or_elim (@lem4816044 _110859 x y t s R h2) (fun h0 : s x => @lem4821825 _110859 x y t s R h0 h1 h2) (fun h0 : t x => @lem4821821 _110859 x y t s R h0 h1 h2)). Qed.
Lemma lem4821839 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : s y) (h2 : term368 _110859 x y t s R) : False.
Proof. exact (or_elim (@lem4816044 _110859 x y t s R h2) (fun h0 : s x => @lem4821833 _110859 x y t s R h0 h1 h2) (fun h0 : t x => @lem4821829 _110859 x y t s R h1 h0 h2)). Qed.
Lemma lem4821840 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term368 _110859 x y t s R) : False.
Proof. exact (or_elim (@lem4816046 _110859 x y t s R h1) (fun h0 : s y => @lem4821839 _110859 x y t s R h0 h1) (fun h0 : t y => @lem4821838 _110859 x y t s R h0 h1)). Qed.
Lemma lem4821841 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term196 _110859 t s R y x) : False.
Proof. exact (or_elim (@lem4816025 _110859 t s R y x h2) (fun h0 : term438 _110859 R x y => @lem4821837 _110859 t s R y x h0 h1 h2) (fun h0 : term438 _110859 R y x => @lem4821835 _110859 t s R y x h0 h1 h2)). Qed.
Lemma lem4821842 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) (h2 : term277 _110859 t s R y x) : False.
Proof. exact (or_elim (@lem4816010 _110859 t s R y x h2) (fun h0 : term160 _110859 t R x y => @lem4818410 _110859 s t R x y h1 h0) (fun h0 : term196 _110859 t s R y x => @lem4821841 _110859 t s R y x h1 h0)). Qed.
Lemma lem4821843 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (y : _110859) (x : _110859) (h1 : term333 _110859 t s R y x) : False.
Proof. exact (or_elim (@lem4816007 _110859 t s R y x h1) (fun h0 : term160 _110859 s R x y => @lem4818065 _110859 t s R x y h1 h0) (fun h0 : term277 _110859 t s R y x => @lem4821842 _110859 t s R y x h1 h0)). Qed.
Lemma lem4821844 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term407 _110859 x y t s R) : False.
Proof. exact (or_elim (@lem4816004 _110859 x y t s R h1) (fun h0 : term333 _110859 t s R y x => @lem4821843 _110859 t s R y x h0) (fun h0 : term368 _110859 x y t s R => @lem4821840 _110859 x y t s R h0)). Qed.
Lemma lem4821845 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term407 _110859 x y t s R) : (term407 _110859 x y t s R) = False.
Proof. exact (prop_ext (fun h2 : term407 _110859 x y t s R => @lem4821844 _110859 x y t s R h1) (fun h2 : False => @lem4816004 _110859 x y t s R h1)). Qed.
Lemma lem4821846 {_110859 : Type'} (x : _110859) (y : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term407 _110859 x y t s R) : False.
Proof. exact (EQ_MP (@lem4821845 _110859 x y t s R h1) (@lem4816004 _110859 x y t s R h1)). Qed.
Lemma lem4821847 {_110859 : Type'} (x : _110859) (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term410 _110859 x t s R) : False.
Proof. exact (ex_elim (@lem4815669 _110859 x t s R h1) (fun y : _110859 => fun h0 : term409 _110859 x t s R y => @lem4821846 _110859 x y t s R h0)). Qed.
Lemma lem4821848 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term114 _110859 t s R) : False.
Proof. exact (ex_elim (@lem4815668 _110859 t s R h1) (fun x : _110859 => fun h0 : term411 _110859 t s R x => @lem4821847 _110859 x t s R h0)). Qed.
Lemma lem4821849 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term114 _110859 t s R) : (term114 _110859 t s R) = False.
Proof. exact (prop_ext (fun h2 : term114 _110859 t s R => @lem4821848 _110859 t s R h1) (fun h2 : False => @lem4814651 _110859 t s R h1)). Qed.
Lemma lem4821850 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) (h1 : term114 _110859 t s R) : False.
Proof. exact (EQ_MP (@lem4821849 _110859 t s R h1) (@lem4814651 _110859 t s R h1)). Qed.
Lemma lem4821851 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : term113 _110859 t s R.
Proof. exact (fun h0 : term114 _110859 t s R => @lem4821850 _110859 t s R h0). Qed.
Lemma lem4821852 {_110859 : Type'} (t : _110859 -> Prop) (s : _110859 -> Prop) (R : type1402 _110859) : (term56 _110859 s t R) = (term98 _110859 t s R).
Proof. exact (EQ_MP (@lem4814650 _110859 t s R) (@lem4821851 _110859 t s R)). Qed.
Lemma lem4821857 {_110859 : Type'} (s : _110859 -> Prop) (R : type1402 _110859) : term100 _110859 s R.
Proof. exact (fun t : _110859 -> Prop => @lem4821852 _110859 t s R). Qed.
Lemma lem4821862 {_110859 : Type'} (R : type1402 _110859) : term102 _110859 R.
Proof. exact (fun s : _110859 -> Prop => @lem4821857 _110859 s R). Qed.
Lemma lem4821867 {_110859 : Type'} : term104 _110859.
Proof. exact (fun R : type1402 _110859 => @lem4821862 _110859 R). Qed.
Lemma lem4821868 {_110859 : Type'} : term106 _110859.
Proof. exact (EQ_MP (@lem4814646 _110859) (@lem4821867 _110859)). Qed.
Lemma lem4821870 {_110859 : Type'} : term106 _110859.
Proof. exact (@lem4814329 _110859 (@lem4821868 _110859)). Qed.
Lemma lem4821871 {_110859 : Type'} (h1 : term107 _110859) : False.
Proof. exact (@lem4821870 _110859 (@lem4814313 _110859 h1)). Qed.
Lemma lem4821872 {_110859 : Type'} (h1 : term107 _110859) : (term107 _110859) = False.
Proof. exact (prop_ext (fun h2 : term107 _110859 => @lem4821871 _110859 h1) (fun h2 : False => @lem4814313 _110859 h1)). Qed.
Lemma lem4821873 {_110859 : Type'} (h1 : term107 _110859) : False.
Proof. exact (EQ_MP (@lem4821872 _110859 h1) (@lem4814313 _110859 h1)). Qed.
Lemma lem4821874 {_110859 : Type'} : term106 _110859.
Proof. exact (fun h0 : term107 _110859 => @lem4821873 _110859 h0). Qed.
Lemma lem4821875 {_110859 : Type'} : term104 _110859.
Proof. exact (EQ_MP (@lem4814312 _110859) (@lem4821874 _110859)). Qed.
Lemma lem4821877 {_110859 : Type'} : term33 _110859.
Proof. exact (EQ_MP (@lem4814308 _110859) (@lem4821875 _110859)). Qed.
Lemma lem4821878 {_110859 : Type'} : term32 _110859.
Proof. exact (EQ_MP (@lem4813885 _110859) (@lem4821877 _110859)). Qed.
