Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_EQ_MEMBERS_EQ_term_abbrevs.
Require Import CARTESIAN_PRODUCT_EQ_MEMBERS_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem4409648 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4409649 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4409650 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4409649 t1) (@lem4409648 t1)). Qed.
Lemma lem4409651 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4409650 t1 t2). Qed.
Lemma lem4409652 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4409653 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4409652 t1 t2) (@lem4409651 t1 t2)). Qed.
Lemma lem4409654 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4409653 t1 t2 t3). Qed.
Lemma lem4409655 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4409656 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4409655 t1 t2 t3) (@lem4409654 t1 t2 t3)). Qed.
Lemma lem4409657 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4409656 t1 t2 t3)). Qed.
Lemma lem4409659 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4409660 {_106189 _106193 : Type'} : (term8 _106189 _106193) = (term9 _106189 _106193).
Proof. exact (@lem4409659 (term8 _106189 _106193)). Qed.
Lemma lem4409661 {_106189 _106193 : Type'} : (term9 _106189 _106193) = (term8 _106189 _106193).
Proof. exact (SYM (@lem4409660 _106189 _106193)). Qed.
Lemma lem4409662 {_106189 _106193 : Type'} (h1 : term10 _106189 _106193) : term10 _106189 _106193.
Proof. exact (h1). Qed.
Lemma lem4409663 {_106189 _106193 : Type'} : term11 _106189 _106193.
Proof. exact (@lem4409647 _106189 _106193). Qed.
Lemma lem4409665 {_106189 _106193 A : Type'} : term12 _106189 _106193 A.
Proof. exact (@lem4409647 A (_106193 -> _106189)). Qed.
Lemma lem4409666 {_106193 A : Type'} : term13 _106193 A.
Proof. exact (@lem4409647 A _106193). Qed.
Lemma lem4409667 {_106189 _106193 K : Type'} : term14 _106189 _106193 K.
Proof. exact (@lem4409647 (_106193 -> _106189) K). Qed.
Lemma lem4409668 {_106189 K : Type'} : term11 _106189 K.
Proof. exact (@lem4409647 _106189 K). Qed.
Lemma lem4409672 {_106189 _106193 A K : Type'} (h1 : term15 _106189 _106193 A K) : term15 _106189 _106193 A K.
Proof. exact (h1). Qed.
Lemma lem4409673 {_106189 _106193 A K : Type'} : term16 _106189 _106193 A K.
Proof. exact (fun h0 : term15 _106189 _106193 A K => @lem4409672 _106189 _106193 A K h0). Qed.
Lemma lem4409674 {_106189 _106193 A K : Type'} (h1 : term16 _106189 _106193 A K) : term16 _106189 _106193 A K.
Proof. exact (h1). Qed.
Lemma lem4409675 {_106189 _106193 A K : Type'} (h1 : term15 _106189 _106193 A K) : term15 _106189 _106193 A K.
Proof. exact (h1). Qed.
Lemma lem4409676 {_106189 _106193 A K : Type'} (h1 : term15 _106189 _106193 A K) (h2 : term16 _106189 _106193 A K) : term15 _106189 _106193 A K.
Proof. exact (@lem4409674 _106189 _106193 A K h2 (@lem4409675 _106189 _106193 A K h1)). Qed.
Lemma lem4409677 {_106189 _106193 A K : Type'} (h1 : term15 _106189 _106193 A K) : term17 _106189 _106193 A K.
Proof. exact (fun h0 : term16 _106189 _106193 A K => @lem4409676 _106189 _106193 A K h1 h0). Qed.
Lemma lem4409678 {_106189 _106193 A K : Type'} (h1 : term16 _106189 _106193 A K) : term16 _106189 _106193 A K.
Proof. exact (h1). Qed.
Lemma lem4409679 {_106189 _106193 A K : Type'} (h1 : term15 _106189 _106193 A K) (h2 : term16 _106189 _106193 A K) : term15 _106189 _106193 A K.
Proof. exact (@lem4409677 _106189 _106193 A K h1 (@lem4409678 _106189 _106193 A K h2)). Qed.
Lemma lem4409680 {_106189 _106193 A K : Type'} (h1 : term16 _106189 _106193 A K) : term16 _106189 _106193 A K.
Proof. exact (fun h0 : term15 _106189 _106193 A K => @lem4409679 _106189 _106193 A K h0 h1). Qed.
Lemma lem4409681 {_106189 _106193 A K : Type'} : term18 _106189 _106193 A K.
Proof. exact (fun h0 : term16 _106189 _106193 A K => @lem4409680 _106189 _106193 A K h0). Qed.
Lemma lem4409684 {_106189 _106193 A K : Type'} : term16 _106189 _106193 A K.
Proof. exact (@lem4409681 _106189 _106193 A K (@lem4409673 _106189 _106193 A K)). Qed.
Lemma lem4409685 {_106189 _106193 A K : Type'} : term16 _106189 _106193 A K.
Proof. exact (@lem4409684 _106189 _106193 A K). Qed.
Lemma lem4409835 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4409836 {_106189 _106193 A : Type'} : (term19 _106189 _106193 A) = (term20 _106189 _106193 A).
Proof. exact (@lem4409835 (term12 _106189 _106193 A)). Qed.
Lemma lem4409865 {_106189 _106193 K : Type'} : (term21 _106189 _106193 K) = (term21 _106189 _106193 K).
Proof. exact (eq_refl (term21 _106189 _106193 K)). Qed.
Lemma lem4409866 {_106189 _106193 A K : Type'} : (term22 _106189 _106193 A K) = (term23 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4409865 _106189 _106193 K) (@lem4409836 _106189 _106193 A)). Qed.
Lemma lem4409869 {_106189 K : Type'} : (term24 _106189 K) = (term24 _106189 K).
Proof. exact (eq_refl (term24 _106189 K)). Qed.
Lemma lem4409870 {_106189 _106193 A K : Type'} : (term25 _106189 _106193 A K) = (term26 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4409869 _106189 K) (@lem4409866 _106189 _106193 A K)). Qed.
Lemma lem4409873 {_106193 A : Type'} : (term27 _106193 A) = (term27 _106193 A).
Proof. exact (eq_refl (term27 _106193 A)). Qed.
Lemma lem4409874 {_106189 _106193 A K : Type'} : (term28 _106189 _106193 A K) = (term29 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4409873 _106193 A) (@lem4409870 _106189 _106193 A K)). Qed.
Lemma lem4409877 {_106189 _106193 : Type'} : (term24 _106189 _106193) = (term24 _106189 _106193).
Proof. exact (eq_refl (term24 _106189 _106193)). Qed.
Lemma lem4409878 {_106189 _106193 A K : Type'} : (term30 _106189 _106193 A K) = (term31 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4409877 _106189 _106193) (@lem4409874 _106189 _106193 A K)). Qed.
Lemma lem4409881 {_106189 _106193 : Type'} : (term32 _106189 _106193) = (term32 _106189 _106193).
Proof. exact (eq_refl (term32 _106189 _106193)). Qed.
Lemma lem4409888 {_106189 _106193 A K : Type'} : (term15 _106189 _106193 A K) = (term33 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4409881 _106189 _106193) (@lem4409878 _106189 _106193 A K)). Qed.
Lemma lem4409889 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4409894 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term34 _106189 _106193 A k x y i) = (term34 _106189 _106193 A k x y i).
Proof. exact (eq_refl (term34 _106189 _106193 A k x y i)). Qed.
Lemma lem4409895 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term35 _106189 _106193 A k x y) = (term35 _106189 _106193 A k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4409894 _106189 _106193 A k x y i)). Qed.
Lemma lem4409896 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4409897 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term36 _106189 _106193 A k x y) = (term36 _106189 _106193 A k x y).
Proof. exact (MK_COMB (@lem4409896 _106189 _106193) (@lem4409895 _106189 _106193 A k x y)). Qed.
Lemma lem4409900 {_106189 _106193 A : Type'} (y : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term37 _106189 _106193 A y k s) = (term37 _106189 _106193 A y k s).
Proof. exact (eq_refl (term37 _106189 _106193 A y k s)). Qed.
Lemma lem4409901 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term38 _106189 _106193 A s k x y) = (term38 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4409900 _106189 _106193 A y k s) (@lem4409897 _106189 _106193 A k x y)). Qed.
Lemma lem4409904 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term37 _106189 _106193 A x k s) = (term37 _106189 _106193 A x k s).
Proof. exact (eq_refl (term37 _106189 _106193 A x k s)). Qed.
Lemma lem4409905 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term39 _106189 _106193 A s k x y) = (term39 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4409904 _106189 _106193 A x k s) (@lem4409901 _106189 _106193 A s k x y)). Qed.
Lemma lem4409906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4409907 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term40 _106189 _106193 A s k x y) = (term40 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4409906) (@lem4409905 _106189 _106193 A s k x y)). Qed.
Lemma lem4409908 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term41 _106189 _106193 A s k x y) = (term41 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4409907 _106189 _106193 A s k x y) (@lem4409889 _106189 _106193 A x y)). Qed.
Lemma lem4409909 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term42 _106189 _106193 A s k x) = (term42 _106189 _106193 A s k x).
Proof. exact (fun_ext (fun y : type804 _106189 _106193 A => @lem4409908 _106189 _106193 A s k x y)). Qed.
Lemma lem4409910 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4409911 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term43 _106189 _106193 A s k x) = (term43 _106189 _106193 A s k x).
Proof. exact (MK_COMB (@lem4409910 _106189 _106193 A) (@lem4409909 _106189 _106193 A s k x)). Qed.
Lemma lem4409912 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term44 _106189 _106193 A s k) = (term44 _106189 _106193 A s k).
Proof. exact (fun_ext (fun x : type804 _106189 _106193 A => @lem4409911 _106189 _106193 A s k x)). Qed.
Lemma lem4409913 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4409914 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term45 _106189 _106193 A s k) = (term45 _106189 _106193 A s k).
Proof. exact (MK_COMB (@lem4409913 _106189 _106193 A) (@lem4409912 _106189 _106193 A s k)). Qed.
Lemma lem4409915 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term46 _106189 _106193 A k) = (term46 _106189 _106193 A k).
Proof. exact (fun_ext (fun s : type800 _106189 _106193 A => @lem4409914 _106189 _106193 A s k)). Qed.
Lemma lem4409916 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A -> Prop)) = (@all ((_106193 -> _106189) -> A -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A -> Prop))). Qed.
Lemma lem4409917 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term47 _106189 _106193 A k) = (term47 _106189 _106193 A k).
Proof. exact (MK_COMB (@lem4409916 _106189 _106193 A) (@lem4409915 _106189 _106193 A k)). Qed.
Lemma lem4409918 {_106189 _106193 A : Type'} : (term48 _106189 _106193 A) = (term48 _106189 _106193 A).
Proof. exact (fun_ext (fun k : type805 _106189 _106193 => @lem4409917 _106189 _106193 A k)). Qed.
Lemma lem4409919 {_106189 _106193 : Type'} : (@all ((_106193 -> _106189) -> Prop)) = (@all ((_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> Prop))). Qed.
Lemma lem4409920 {_106189 _106193 A : Type'} : (term12 _106189 _106193 A) = (term12 _106189 _106193 A).
Proof. exact (MK_COMB (@lem4409919 _106189 _106193) (@lem4409918 _106189 _106193 A)). Qed.
Lemma lem4409921 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4409922 {_106189 _106193 A : Type'} : (term20 _106189 _106193 A) = (term20 _106189 _106193 A).
Proof. exact (MK_COMB (@lem4409921) (@lem4409920 _106189 _106193 A)). Qed.
Lemma lem4409923 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4409928 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term49 _106189 _106193 K k x y i) = (term49 _106189 _106193 K k x y i).
Proof. exact (eq_refl (term49 _106189 _106193 K k x y i)). Qed.
Lemma lem4409929 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term50 _106189 _106193 K k x y) = (term50 _106189 _106193 K k x y).
Proof. exact (fun_ext (fun i : K => @lem4409928 _106189 _106193 K k x y i)). Qed.
Lemma lem4409930 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4409931 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term51 _106189 _106193 K k x y) = (term51 _106189 _106193 K k x y).
Proof. exact (MK_COMB (@lem4409930 K) (@lem4409929 _106189 _106193 K k x y)). Qed.
Lemma lem4409934 {_106189 _106193 K : Type'} (y : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term52 _106189 _106193 K y k s) = (term52 _106189 _106193 K y k s).
Proof. exact (eq_refl (term52 _106189 _106193 K y k s)). Qed.
Lemma lem4409935 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term53 _106189 _106193 K s k x y) = (term53 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4409934 _106189 _106193 K y k s) (@lem4409931 _106189 _106193 K k x y)). Qed.
Lemma lem4409938 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term52 _106189 _106193 K x k s) = (term52 _106189 _106193 K x k s).
Proof. exact (eq_refl (term52 _106189 _106193 K x k s)). Qed.
Lemma lem4409939 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term54 _106189 _106193 K s k x y) = (term54 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4409938 _106189 _106193 K x k s) (@lem4409935 _106189 _106193 K s k x y)). Qed.
Lemma lem4409940 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4409941 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term55 _106189 _106193 K s k x y) = (term55 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4409940) (@lem4409939 _106189 _106193 K s k x y)). Qed.
Lemma lem4409942 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term56 _106189 _106193 K s k x y) = (term56 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4409941 _106189 _106193 K s k x y) (@lem4409923 _106189 _106193 K x y)). Qed.
Lemma lem4409943 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term57 _106189 _106193 K s k x) = (term57 _106189 _106193 K s k x).
Proof. exact (fun_ext (fun y : type1518 _106189 _106193 K => @lem4409942 _106189 _106193 K s k x y)). Qed.
Lemma lem4409944 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4409945 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term58 _106189 _106193 K s k x) = (term58 _106189 _106193 K s k x).
Proof. exact (MK_COMB (@lem4409944 _106189 _106193 K) (@lem4409943 _106189 _106193 K s k x)). Qed.
Lemma lem4409946 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term59 _106189 _106193 K s k) = (term59 _106189 _106193 K s k).
Proof. exact (fun_ext (fun x : type1518 _106189 _106193 K => @lem4409945 _106189 _106193 K s k x)). Qed.
Lemma lem4409947 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4409948 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term60 _106189 _106193 K s k) = (term60 _106189 _106193 K s k).
Proof. exact (MK_COMB (@lem4409947 _106189 _106193 K) (@lem4409946 _106189 _106193 K s k)). Qed.
Lemma lem4409949 {_106189 _106193 K : Type'} (k : K -> Prop) : (term61 _106189 _106193 K k) = (term61 _106189 _106193 K k).
Proof. exact (fun_ext (fun s : type1508 _106189 _106193 K => @lem4409948 _106189 _106193 K s k)). Qed.
Lemma lem4409950 {_106189 _106193 K : Type'} : (@all (K -> (_106193 -> _106189) -> Prop)) = (@all (K -> (_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all (K -> (_106193 -> _106189) -> Prop))). Qed.
Lemma lem4409951 {_106189 _106193 K : Type'} (k : K -> Prop) : (term62 _106189 _106193 K k) = (term62 _106189 _106193 K k).
Proof. exact (MK_COMB (@lem4409950 _106189 _106193 K) (@lem4409949 _106189 _106193 K k)). Qed.
Lemma lem4409952 {_106189 _106193 K : Type'} : (term63 _106189 _106193 K) = (term63 _106189 _106193 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4409951 _106189 _106193 K k)). Qed.
Lemma lem4409953 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4409954 {_106189 _106193 K : Type'} : (term14 _106189 _106193 K) = (term14 _106189 _106193 K).
Proof. exact (MK_COMB (@lem4409953 K) (@lem4409952 _106189 _106193 K)). Qed.
Lemma lem4409955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4409956 {_106189 _106193 K : Type'} : (term21 _106189 _106193 K) = (term21 _106189 _106193 K).
Proof. exact (MK_COMB (@lem4409955) (@lem4409954 _106189 _106193 K)). Qed.
Lemma lem4409957 {_106189 _106193 A K : Type'} : (term23 _106189 _106193 A K) = (term23 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4409956 _106189 _106193 K) (@lem4409922 _106189 _106193 A)). Qed.
Lemma lem4409958 {_106189 K : Type'} (x : K -> _106189) (y : K -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4409963 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term64 _106189 K k x y i) = (term64 _106189 K k x y i).
Proof. exact (eq_refl (term64 _106189 K k x y i)). Qed.
Lemma lem4409964 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term65 _106189 K k x y) = (term65 _106189 K k x y).
Proof. exact (fun_ext (fun i : K => @lem4409963 _106189 K k x y i)). Qed.
Lemma lem4409965 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4409966 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term66 _106189 K k x y) = (term66 _106189 K k x y).
Proof. exact (MK_COMB (@lem4409965 K) (@lem4409964 _106189 K k x y)). Qed.
Lemma lem4409969 {_106189 K : Type'} (y : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term67 _106189 K y k s) = (term67 _106189 K y k s).
Proof. exact (eq_refl (term67 _106189 K y k s)). Qed.
Lemma lem4409970 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term68 _106189 K s k x y) = (term68 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4409969 _106189 K y k s) (@lem4409966 _106189 K k x y)). Qed.
Lemma lem4409973 {_106189 K : Type'} (x : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term67 _106189 K x k s) = (term67 _106189 K x k s).
Proof. exact (eq_refl (term67 _106189 K x k s)). Qed.
Lemma lem4409974 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term69 _106189 K s k x y) = (term69 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4409973 _106189 K x k s) (@lem4409970 _106189 K s k x y)). Qed.
Lemma lem4409975 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4409976 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term70 _106189 K s k x y) = (term70 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4409975) (@lem4409974 _106189 K s k x y)). Qed.
Lemma lem4409977 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term71 _106189 K s k x y) = (term71 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4409976 _106189 K s k x y) (@lem4409958 _106189 K x y)). Qed.
Lemma lem4409978 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term72 _106189 K s k x) = (term72 _106189 K s k x).
Proof. exact (fun_ext (fun y : K -> _106189 => @lem4409977 _106189 K s k x y)). Qed.
Lemma lem4409979 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4409980 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term73 _106189 K s k x) = (term73 _106189 K s k x).
Proof. exact (MK_COMB (@lem4409979 _106189 K) (@lem4409978 _106189 K s k x)). Qed.
Lemma lem4409981 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term74 _106189 K s k) = (term74 _106189 K s k).
Proof. exact (fun_ext (fun x : K -> _106189 => @lem4409980 _106189 K s k x)). Qed.
Lemma lem4409982 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4409983 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term75 _106189 K s k) = (term75 _106189 K s k).
Proof. exact (MK_COMB (@lem4409982 _106189 K) (@lem4409981 _106189 K s k)). Qed.
Lemma lem4409984 {_106189 K : Type'} (k : K -> Prop) : (term76 _106189 K k) = (term76 _106189 K k).
Proof. exact (fun_ext (fun s : type1470 _106189 K => @lem4409983 _106189 K s k)). Qed.
Lemma lem4409985 {_106189 K : Type'} : (@all (K -> _106189 -> Prop)) = (@all (K -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (K -> _106189 -> Prop))). Qed.
Lemma lem4409986 {_106189 K : Type'} (k : K -> Prop) : (term77 _106189 K k) = (term77 _106189 K k).
Proof. exact (MK_COMB (@lem4409985 _106189 K) (@lem4409984 _106189 K k)). Qed.
Lemma lem4409987 {_106189 K : Type'} : (term78 _106189 K) = (term78 _106189 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4409986 _106189 K k)). Qed.
Lemma lem4409988 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4409989 {_106189 K : Type'} : (term11 _106189 K) = (term11 _106189 K).
Proof. exact (MK_COMB (@lem4409988 K) (@lem4409987 _106189 K)). Qed.
Lemma lem4409990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4409991 {_106189 K : Type'} : (term24 _106189 K) = (term24 _106189 K).
Proof. exact (MK_COMB (@lem4409990) (@lem4409989 _106189 K)). Qed.
Lemma lem4409992 {_106189 _106193 A K : Type'} : (term26 _106189 _106193 A K) = (term26 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4409991 _106189 K) (@lem4409957 _106189 _106193 A K)). Qed.
Lemma lem4409993 {_106193 A : Type'} (x : _106193 -> A) (y : _106193 -> A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4409998 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term79 _106193 A k x y i) = (term79 _106193 A k x y i).
Proof. exact (eq_refl (term79 _106193 A k x y i)). Qed.
Lemma lem4409999 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term80 _106193 A k x y) = (term80 _106193 A k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4409998 _106193 A k x y i)). Qed.
Lemma lem4410000 {_106193 : Type'} : (@all _106193) = (@all _106193).
Proof. exact (eq_refl (@all _106193)). Qed.
Lemma lem4410001 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term81 _106193 A k x y) = (term81 _106193 A k x y).
Proof. exact (MK_COMB (@lem4410000 _106193) (@lem4409999 _106193 A k x y)). Qed.
Lemma lem4410004 {_106193 A : Type'} (y : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term82 _106193 A y k s) = (term82 _106193 A y k s).
Proof. exact (eq_refl (term82 _106193 A y k s)). Qed.
Lemma lem4410005 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term83 _106193 A s k x y) = (term83 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4410004 _106193 A y k s) (@lem4410001 _106193 A k x y)). Qed.
Lemma lem4410008 {_106193 A : Type'} (x : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term82 _106193 A x k s) = (term82 _106193 A x k s).
Proof. exact (eq_refl (term82 _106193 A x k s)). Qed.
Lemma lem4410009 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term84 _106193 A s k x y) = (term84 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4410008 _106193 A x k s) (@lem4410005 _106193 A s k x y)). Qed.
Lemma lem4410010 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4410011 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term85 _106193 A s k x y) = (term85 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4410010) (@lem4410009 _106193 A s k x y)). Qed.
Lemma lem4410012 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term86 _106193 A s k x y) = (term86 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4410011 _106193 A s k x y) (@lem4409993 _106193 A x y)). Qed.
Lemma lem4410013 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term87 _106193 A s k x) = (term87 _106193 A s k x).
Proof. exact (fun_ext (fun y : _106193 -> A => @lem4410012 _106193 A s k x y)). Qed.
Lemma lem4410014 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4410015 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term88 _106193 A s k x) = (term88 _106193 A s k x).
Proof. exact (MK_COMB (@lem4410014 _106193 A) (@lem4410013 _106193 A s k x)). Qed.
Lemma lem4410016 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term89 _106193 A s k) = (term89 _106193 A s k).
Proof. exact (fun_ext (fun x : _106193 -> A => @lem4410015 _106193 A s k x)). Qed.
Lemma lem4410017 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4410018 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term90 _106193 A s k) = (term90 _106193 A s k).
Proof. exact (MK_COMB (@lem4410017 _106193 A) (@lem4410016 _106193 A s k)). Qed.
Lemma lem4410019 {_106193 A : Type'} (k : _106193 -> Prop) : (term91 _106193 A k) = (term91 _106193 A k).
Proof. exact (fun_ext (fun s : type1413 _106193 A => @lem4410018 _106193 A s k)). Qed.
Lemma lem4410020 {_106193 A : Type'} : (@all (_106193 -> A -> Prop)) = (@all (_106193 -> A -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> A -> Prop))). Qed.
Lemma lem4410021 {_106193 A : Type'} (k : _106193 -> Prop) : (term92 _106193 A k) = (term92 _106193 A k).
Proof. exact (MK_COMB (@lem4410020 _106193 A) (@lem4410019 _106193 A k)). Qed.
Lemma lem4410022 {_106193 A : Type'} : (term93 _106193 A) = (term93 _106193 A).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4410021 _106193 A k)). Qed.
Lemma lem4410023 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4410024 {_106193 A : Type'} : (term13 _106193 A) = (term13 _106193 A).
Proof. exact (MK_COMB (@lem4410023 _106193) (@lem4410022 _106193 A)). Qed.
Lemma lem4410025 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4410026 {_106193 A : Type'} : (term27 _106193 A) = (term27 _106193 A).
Proof. exact (MK_COMB (@lem4410025) (@lem4410024 _106193 A)). Qed.
Lemma lem4410027 {_106189 _106193 A K : Type'} : (term29 _106189 _106193 A K) = (term29 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4410026 _106193 A) (@lem4409992 _106189 _106193 A K)). Qed.
Lemma lem4410028 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4410033 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term64 _106189 _106193 k x y i) = (term64 _106189 _106193 k x y i).
Proof. exact (eq_refl (term64 _106189 _106193 k x y i)). Qed.
Lemma lem4410034 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term65 _106189 _106193 k x y) = (term65 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410033 _106189 _106193 k x y i)). Qed.
Lemma lem4410035 {_106193 : Type'} : (@all _106193) = (@all _106193).
Proof. exact (eq_refl (@all _106193)). Qed.
Lemma lem4410036 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term66 _106189 _106193 k x y) = (term66 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410035 _106193) (@lem4410034 _106189 _106193 k x y)). Qed.
Lemma lem4410039 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term67 _106189 _106193 y k s) = (term67 _106189 _106193 y k s).
Proof. exact (eq_refl (term67 _106189 _106193 y k s)). Qed.
Lemma lem4410040 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term68 _106189 _106193 s k x y) = (term68 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410039 _106189 _106193 y k s) (@lem4410036 _106189 _106193 k x y)). Qed.
Lemma lem4410043 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term67 _106189 _106193 x k s) = (term67 _106189 _106193 x k s).
Proof. exact (eq_refl (term67 _106189 _106193 x k s)). Qed.
Lemma lem4410044 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term69 _106189 _106193 s k x y) = (term69 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410043 _106189 _106193 x k s) (@lem4410040 _106189 _106193 s k x y)). Qed.
Lemma lem4410045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4410046 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term70 _106189 _106193 s k x y) = (term70 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410045) (@lem4410044 _106189 _106193 s k x y)). Qed.
Lemma lem4410047 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term71 _106189 _106193 s k x y) = (term71 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410046 _106189 _106193 s k x y) (@lem4410028 _106189 _106193 x y)). Qed.
Lemma lem4410048 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term72 _106189 _106193 s k x) = (term72 _106189 _106193 s k x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410047 _106189 _106193 s k x y)). Qed.
Lemma lem4410049 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410050 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term73 _106189 _106193 s k x) = (term73 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410049 _106189 _106193) (@lem4410048 _106189 _106193 s k x)). Qed.
Lemma lem4410051 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term74 _106189 _106193 s k) = (term74 _106189 _106193 s k).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410050 _106189 _106193 s k x)). Qed.
Lemma lem4410052 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410053 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term75 _106189 _106193 s k) = (term75 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410052 _106189 _106193) (@lem4410051 _106189 _106193 s k)). Qed.
Lemma lem4410054 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term76 _106189 _106193 k) = (term76 _106189 _106193 k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4410053 _106189 _106193 s k)). Qed.
Lemma lem4410055 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4410056 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term77 _106189 _106193 k) = (term77 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410055 _106189 _106193) (@lem4410054 _106189 _106193 k)). Qed.
Lemma lem4410057 {_106189 _106193 : Type'} : (term78 _106189 _106193) = (term78 _106189 _106193).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4410056 _106189 _106193 k)). Qed.
Lemma lem4410058 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4410059 {_106189 _106193 : Type'} : (term11 _106189 _106193) = (term11 _106189 _106193).
Proof. exact (MK_COMB (@lem4410058 _106193) (@lem4410057 _106189 _106193)). Qed.
Lemma lem4410060 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4410061 {_106189 _106193 : Type'} : (term24 _106189 _106193) = (term24 _106189 _106193).
Proof. exact (MK_COMB (@lem4410060) (@lem4410059 _106189 _106193)). Qed.
Lemma lem4410062 {_106189 _106193 A K : Type'} : (term31 _106189 _106193 A K) = (term31 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4410061 _106189 _106193) (@lem4410027 _106189 _106193 A K)). Qed.
Lemma lem4410067 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term64 _106189 _106193 k x y i) = (term64 _106189 _106193 k x y i).
Proof. exact (eq_refl (term64 _106189 _106193 k x y i)). Qed.
Lemma lem4410068 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term65 _106189 _106193 k x y) = (term65 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410067 _106189 _106193 k x y i)). Qed.
Lemma lem4410069 {_106193 : Type'} : (@all _106193) = (@all _106193).
Proof. exact (eq_refl (@all _106193)). Qed.
Lemma lem4410070 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term66 _106189 _106193 k x y) = (term66 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410069 _106193) (@lem4410068 _106189 _106193 k x y)). Qed.
Lemma lem4410073 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term94 _106189 _106193 x y) = (term94 _106189 _106193 x y).
Proof. exact (eq_refl (term94 _106189 _106193 x y)). Qed.
Lemma lem4410074 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((x = y) = (term66 _106189 _106193 k x y)) = ((x = y) = (term66 _106189 _106193 k x y)).
Proof. exact (MK_COMB (@lem4410073 _106189 _106193 x y) (@lem4410070 _106189 _106193 k x y)). Qed.
Lemma lem4410081 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term95 _106189 _106193 x y k s) = (term95 _106189 _106193 x y k s).
Proof. exact (eq_refl (term95 _106189 _106193 x y k s)). Qed.
Lemma lem4410082 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term96 _106189 _106193 s k x y) = (term96 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410081 _106189 _106193 x y k s) (@lem4410074 _106189 _106193 k x y)). Qed.
Lemma lem4410083 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term97 _106189 _106193 s k x) = (term97 _106189 _106193 s k x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410082 _106189 _106193 s k x y)). Qed.
Lemma lem4410084 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410085 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term98 _106189 _106193 s k x) = (term98 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410084 _106189 _106193) (@lem4410083 _106189 _106193 s k x)). Qed.
Lemma lem4410086 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term99 _106189 _106193 s k) = (term99 _106189 _106193 s k).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410085 _106189 _106193 s k x)). Qed.
Lemma lem4410087 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410088 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term100 _106189 _106193 s k) = (term100 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410087 _106189 _106193) (@lem4410086 _106189 _106193 s k)). Qed.
Lemma lem4410089 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term101 _106189 _106193 k) = (term101 _106189 _106193 k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4410088 _106189 _106193 s k)). Qed.
Lemma lem4410090 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4410091 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term102 _106189 _106193 k) = (term102 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410090 _106189 _106193) (@lem4410089 _106189 _106193 k)). Qed.
Lemma lem4410092 {_106189 _106193 : Type'} : (term103 _106189 _106193) = (term103 _106189 _106193).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4410091 _106189 _106193 k)). Qed.
Lemma lem4410093 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4410094 {_106189 _106193 : Type'} : (term8 _106189 _106193) = (term8 _106189 _106193).
Proof. exact (MK_COMB (@lem4410093 _106193) (@lem4410092 _106189 _106193)). Qed.
Lemma lem4410095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4410096 {_106189 _106193 : Type'} : (term10 _106189 _106193) = (term10 _106189 _106193).
Proof. exact (MK_COMB (@lem4410095) (@lem4410094 _106189 _106193)). Qed.
Lemma lem4410097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4410098 {_106189 _106193 : Type'} : (term32 _106189 _106193) = (term32 _106189 _106193).
Proof. exact (MK_COMB (@lem4410097) (@lem4410096 _106189 _106193)). Qed.
Lemma lem4410099 {_106189 _106193 A K : Type'} : (term33 _106189 _106193 A K) = (term33 _106189 _106193 A K).
Proof. exact (MK_COMB (@lem4410098 _106189 _106193) (@lem4410062 _106189 _106193 A K)). Qed.
Lemma lem4410338 {_106189 _106193 A K : Type'} : (term15 _106189 _106193 A K) = (term33 _106189 _106193 A K).
Proof. exact (TRANS (@lem4409888 _106189 _106193 A K) (@lem4410099 _106189 _106193 A K)). Qed.
Lemma lem4410339 {_106189 _106193 A K : Type'} : (term33 _106189 _106193 A K) = (term15 _106189 _106193 A K).
Proof. exact (SYM (@lem4410338 _106189 _106193 A K)). Qed.
Lemma lem4410340 {_106189 _106193 : Type'} (h1 : term10 _106189 _106193) : term10 _106189 _106193.
Proof. exact (h1). Qed.
Lemma lem4410341 {_106189 _106193 : Type'} (h1 : term11 _106189 _106193) : term11 _106189 _106193.
Proof. exact (h1). Qed.
Lemma lem4410342 {_106193 A : Type'} (h1 : term13 _106193 A) : term13 _106193 A.
Proof. exact (h1). Qed.
Lemma lem4410343 {_106189 K : Type'} (h1 : term11 _106189 K) : term11 _106189 K.
Proof. exact (h1). Qed.
Lemma lem4410344 {_106189 _106193 K : Type'} (h1 : term14 _106189 _106193 K) : term14 _106189 _106193 K.
Proof. exact (h1). Qed.
Lemma lem4410345 {_106189 _106193 A : Type'} (h1 : term12 _106189 _106193 A) : term12 _106189 _106193 A.
Proof. exact (h1). Qed.
Lemma lem4410361 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term104 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (@lem17362 (@IN _106193 i k) ((x i) = (y i))). Qed.
Lemma lem4410366 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term64 _106189 _106193 k x y i) = (term106 _106189 _106193 k x y i).
Proof. exact (@lem17265 (@IN _106193 i k) ((x i) = (y i))). Qed.
Lemma lem4410367 {_106193 : Type'} (P : _106193 -> Prop) : (term107 _106193 P) = (term108 _106193 P).
Proof. exact (@lem18392 _106193 P). Qed.
Lemma lem4410368 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term109 _106189 _106193 k x y) = (term110 _106189 _106193 k x y).
Proof. exact (@lem4410367 _106193 (term65 _106189 _106193 k x y)). Qed.
Lemma lem4410369 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term111 _106189 _106193 k x y i) = (term64 _106189 _106193 k x y i).
Proof. exact (eq_refl (term111 _106189 _106193 k x y i)). Qed.
Lemma lem4410370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4410371 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term112 _106189 _106193 k x y i) = (term104 _106189 _106193 k x y i).
Proof. exact (MK_COMB (@lem4410370) (@lem4410369 _106189 _106193 k x y i)). Qed.
Lemma lem4410372 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term112 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (TRANS (@lem4410371 _106189 _106193 k x y i) (@lem4410361 _106189 _106193 k x y i)). Qed.
Lemma lem4410373 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term113 _106189 _106193 k x y) = (term114 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410372 _106189 _106193 k x y i)). Qed.
Lemma lem4410374 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410375 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term110 _106189 _106193 k x y) = (term115 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410374 _106193) (@lem4410373 _106189 _106193 k x y)). Qed.
Lemma lem4410376 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term109 _106189 _106193 k x y) = (term115 _106189 _106193 k x y).
Proof. exact (TRANS (@lem4410368 _106189 _106193 k x y) (@lem4410375 _106189 _106193 k x y)). Qed.
Lemma lem4410377 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term65 _106189 _106193 k x y) = (term116 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410366 _106189 _106193 k x y i)). Qed.
Lemma lem4410378 {_106193 : Type'} : (@all _106193) = (@all _106193).
Proof. exact (eq_refl (@all _106193)). Qed.
Lemma lem4410379 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term66 _106189 _106193 k x y) = (term117 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410378 _106193) (@lem4410377 _106189 _106193 k x y)). Qed.
Lemma lem4410381 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term118 _106189 _106193 x y) = (term118 _106189 _106193 x y).
Proof. exact (eq_refl (term118 _106189 _106193 x y)). Qed.
Lemma lem4410382 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term119 _106189 _106193 k x y) = (term120 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410381 _106189 _106193 x y) (@lem4410379 _106189 _106193 k x y)). Qed.
Lemma lem4410384 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term121 _106189 _106193 x y) = (term121 _106189 _106193 x y).
Proof. exact (eq_refl (term121 _106189 _106193 x y)). Qed.
Lemma lem4410385 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term122 _106189 _106193 k x y) = (term123 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410384 _106189 _106193 x y) (@lem4410376 _106189 _106193 k x y)). Qed.
Lemma lem4410386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410387 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term124 _106189 _106193 k x y) = (term125 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410386) (@lem4410385 _106189 _106193 k x y)). Qed.
Lemma lem4410388 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term126 _106189 _106193 k x y) = (term127 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410387 _106189 _106193 k x y) (@lem4410382 _106189 _106193 k x y)). Qed.
Lemma lem4410389 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term128 _106189 _106193 k x y) = (term126 _106189 _106193 k x y).
Proof. exact (@lem17646 (x = y) (term66 _106189 _106193 k x y)). Qed.
Lemma lem4410390 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term128 _106189 _106193 k x y) = (term127 _106189 _106193 k x y).
Proof. exact (TRANS (@lem4410389 _106189 _106193 k x y) (@lem4410388 _106189 _106193 k x y)). Qed.
Lemma lem4410392 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term129 _106189 _106193 x y k s) = (term129 _106189 _106193 x y k s).
Proof. exact (eq_refl (term129 _106189 _106193 x y k s)). Qed.
Lemma lem4410393 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term130 _106189 _106193 s k x y) = (term131 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410392 _106189 _106193 x y k s) (@lem4410390 _106189 _106193 k x y)). Qed.
Lemma lem4410394 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term132 _106189 _106193 s k x y) = (term130 _106189 _106193 s k x y).
Proof. exact (@lem17362 (term133 _106189 _106193 x y k s) ((x = y) = (term66 _106189 _106193 k x y))). Qed.
Lemma lem4410395 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term132 _106189 _106193 s k x y) = (term131 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410394 _106189 _106193 s k x y) (@lem4410393 _106189 _106193 s k x y)). Qed.
Lemma lem4410396 {_106189 _106193 : Type'} (P : type805 _106189 _106193) : (term134 _106189 _106193 P) = (term135 _106189 _106193 P).
Proof. exact (@lem18392 (_106193 -> _106189) P). Qed.
Lemma lem4410397 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term136 _106189 _106193 s k x) = (term137 _106189 _106193 s k x).
Proof. exact (@lem4410396 _106189 _106193 (term97 _106189 _106193 s k x)). Qed.
Lemma lem4410398 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term138 _106189 _106193 s k x y) = (term96 _106189 _106193 s k x y).
Proof. exact (eq_refl (term138 _106189 _106193 s k x y)). Qed.
Lemma lem4410399 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4410400 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term139 _106189 _106193 s k x y) = (term132 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410399) (@lem4410398 _106189 _106193 s k x y)). Qed.
Lemma lem4410401 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term139 _106189 _106193 s k x y) = (term131 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410400 _106189 _106193 s k x y) (@lem4410395 _106189 _106193 s k x y)). Qed.
Lemma lem4410402 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term140 _106189 _106193 s k x) = (term141 _106189 _106193 s k x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410401 _106189 _106193 s k x y)). Qed.
Lemma lem4410403 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4410404 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term137 _106189 _106193 s k x) = (term142 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410403 _106189 _106193) (@lem4410402 _106189 _106193 s k x)). Qed.
Lemma lem4410405 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term136 _106189 _106193 s k x) = (term142 _106189 _106193 s k x).
Proof. exact (TRANS (@lem4410397 _106189 _106193 s k x) (@lem4410404 _106189 _106193 s k x)). Qed.
Lemma lem4410406 {_106189 _106193 : Type'} (P : type805 _106189 _106193) : (term134 _106189 _106193 P) = (term135 _106189 _106193 P).
Proof. exact (@lem18392 (_106193 -> _106189) P). Qed.
Lemma lem4410407 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term143 _106189 _106193 s k) = (term144 _106189 _106193 s k).
Proof. exact (@lem4410406 _106189 _106193 (term99 _106189 _106193 s k)). Qed.
Lemma lem4410408 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term145 _106189 _106193 s k x) = (term98 _106189 _106193 s k x).
Proof. exact (eq_refl (term145 _106189 _106193 s k x)). Qed.
Lemma lem4410409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4410410 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term146 _106189 _106193 s k x) = (term136 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410409) (@lem4410408 _106189 _106193 s k x)). Qed.
Lemma lem4410411 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term146 _106189 _106193 s k x) = (term142 _106189 _106193 s k x).
Proof. exact (TRANS (@lem4410410 _106189 _106193 s k x) (@lem4410405 _106189 _106193 s k x)). Qed.
Lemma lem4410412 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term147 _106189 _106193 s k) = (term148 _106189 _106193 s k).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410411 _106189 _106193 s k x)). Qed.
Lemma lem4410413 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4410414 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term144 _106189 _106193 s k) = (term149 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410413 _106189 _106193) (@lem4410412 _106189 _106193 s k)). Qed.
Lemma lem4410415 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term143 _106189 _106193 s k) = (term149 _106189 _106193 s k).
Proof. exact (TRANS (@lem4410407 _106189 _106193 s k) (@lem4410414 _106189 _106193 s k)). Qed.
Lemma lem4410416 {_106189 _106193 : Type'} (P : type745 _106189 _106193) : (term150 _106189 _106193 P) = (term151 _106189 _106193 P).
Proof. exact (@lem18392 (type1470 _106189 _106193) P). Qed.
Lemma lem4410417 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term152 _106189 _106193 k) = (term153 _106189 _106193 k).
Proof. exact (@lem4410416 _106189 _106193 (term101 _106189 _106193 k)). Qed.
Lemma lem4410418 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term154 _106189 _106193 k s) = (term100 _106189 _106193 s k).
Proof. exact (eq_refl (term154 _106189 _106193 k s)). Qed.
Lemma lem4410419 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4410420 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term155 _106189 _106193 k s) = (term143 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410419) (@lem4410418 _106189 _106193 s k)). Qed.
Lemma lem4410421 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term155 _106189 _106193 k s) = (term149 _106189 _106193 s k).
Proof. exact (TRANS (@lem4410420 _106189 _106193 s k) (@lem4410415 _106189 _106193 s k)). Qed.
Lemma lem4410422 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term156 _106189 _106193 k) = (term157 _106189 _106193 k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4410421 _106189 _106193 s k)). Qed.
Lemma lem4410423 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189 -> Prop)) = (@ex (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@ex (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4410424 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term153 _106189 _106193 k) = (term158 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410423 _106189 _106193) (@lem4410422 _106189 _106193 k)). Qed.
Lemma lem4410425 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term152 _106189 _106193 k) = (term158 _106189 _106193 k).
Proof. exact (TRANS (@lem4410417 _106189 _106193 k) (@lem4410424 _106189 _106193 k)). Qed.
Lemma lem4410426 {_106193 : Type'} (P : type686 _106193) : (term159 _106193 P) = (term160 _106193 P).
Proof. exact (@lem18392 (_106193 -> Prop) P). Qed.
Lemma lem4410427 {_106189 _106193 : Type'} : (term10 _106189 _106193) = (term161 _106189 _106193).
Proof. exact (@lem4410426 _106193 (term103 _106189 _106193)). Qed.
Lemma lem4410428 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term162 _106189 _106193 k) = (term102 _106189 _106193 k).
Proof. exact (eq_refl (term162 _106189 _106193 k)). Qed.
Lemma lem4410429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4410430 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term163 _106189 _106193 k) = (term152 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410429) (@lem4410428 _106189 _106193 k)). Qed.
Lemma lem4410431 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term163 _106189 _106193 k) = (term158 _106189 _106193 k).
Proof. exact (TRANS (@lem4410430 _106189 _106193 k) (@lem4410425 _106189 _106193 k)). Qed.
Lemma lem4410432 {_106189 _106193 : Type'} : (term164 _106189 _106193) = (term165 _106189 _106193).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4410431 _106189 _106193 k)). Qed.
Lemma lem4410433 {_106193 : Type'} : (@ex (_106193 -> Prop)) = (@ex (_106193 -> Prop)).
Proof. exact (eq_refl (@ex (_106193 -> Prop))). Qed.
Lemma lem4410434 {_106189 _106193 : Type'} : (term161 _106189 _106193) = (term166 _106189 _106193).
Proof. exact (MK_COMB (@lem4410433 _106193) (@lem4410432 _106189 _106193)). Qed.
Lemma lem4410435 {_106189 _106193 : Type'} : (term10 _106189 _106193) = (term166 _106189 _106193).
Proof. exact (TRANS (@lem4410427 _106189 _106193) (@lem4410434 _106189 _106193)). Qed.
Lemma lem4410594 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4410595 {_106193 : Type'} (P : Prop) (Q : _106193 -> Prop) : (term167 _106193 P Q) = (term168 _106193 P Q).
Proof. exact (@lem4410594 _106193 P Q). Qed.
Lemma lem4410596 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term169 _106189 _106193 k x y) = (term170 _106189 _106193 k x y).
Proof. exact (@lem4410595 _106193 (x = y) (term114 _106189 _106193 k x y)). Qed.
Lemma lem4410597 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term171 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (eq_refl (term171 _106189 _106193 k x y i)). Qed.
Lemma lem4410598 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term172 _106189 _106193 k x y) = (term114 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410597 _106189 _106193 k x y i)). Qed.
Lemma lem4410599 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410600 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term173 _106189 _106193 k x y) = (term115 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410599 _106193) (@lem4410598 _106189 _106193 k x y)). Qed.
Lemma lem4410601 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term121 _106189 _106193 x y) = (term121 _106189 _106193 x y).
Proof. exact (eq_refl (term121 _106189 _106193 x y)). Qed.
Lemma lem4410602 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term169 _106189 _106193 k x y) = (term123 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410601 _106189 _106193 x y) (@lem4410600 _106189 _106193 k x y)). Qed.
Lemma lem4410603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410604 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term174 _106189 _106193 k x y) = (term175 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410603) (@lem4410602 _106189 _106193 k x y)). Qed.
Lemma lem4410605 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term171 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (eq_refl (term171 _106189 _106193 k x y i)). Qed.
Lemma lem4410606 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term121 _106189 _106193 x y) = (term121 _106189 _106193 x y).
Proof. exact (eq_refl (term121 _106189 _106193 x y)). Qed.
Lemma lem4410607 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term176 _106189 _106193 k x y i) = (term177 _106189 _106193 k x y i).
Proof. exact (MK_COMB (@lem4410606 _106189 _106193 x y) (@lem4410605 _106189 _106193 k x y i)). Qed.
Lemma lem4410608 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term178 _106189 _106193 k x y) = (term179 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410607 _106189 _106193 k x y i)). Qed.
Lemma lem4410609 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410610 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term170 _106189 _106193 k x y) = (term180 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410609 _106193) (@lem4410608 _106189 _106193 k x y)). Qed.
Lemma lem4410611 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((term169 _106189 _106193 k x y) = (term170 _106189 _106193 k x y)) = ((term123 _106189 _106193 k x y) = (term180 _106189 _106193 k x y)).
Proof. exact (MK_COMB (@lem4410604 _106189 _106193 k x y) (@lem4410610 _106189 _106193 k x y)). Qed.
Lemma lem4410612 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term123 _106189 _106193 k x y) = (term180 _106189 _106193 k x y).
Proof. exact (EQ_MP (@lem4410611 _106189 _106193 k x y) (@lem4410596 _106189 _106193 k x y)). Qed.
Lemma lem4410613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410614 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term125 _106189 _106193 k x y) = (term181 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410613) (@lem4410612 _106189 _106193 k x y)). Qed.
Lemma lem4410615 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term120 _106189 _106193 k x y) = (term120 _106189 _106193 k x y).
Proof. exact (eq_refl (term120 _106189 _106193 k x y)). Qed.
Lemma lem4410616 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term127 _106189 _106193 k x y) = (term182 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410614 _106189 _106193 k x y) (@lem4410615 _106189 _106193 k x y)). Qed.
Lemma lem4410618 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4410619 {_106193 : Type'} (P : _106193 -> Prop) (Q : Prop) : (term183 _106193 P Q) = (term184 _106193 P Q).
Proof. exact (@lem4410618 _106193 P Q). Qed.
Lemma lem4410620 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term185 _106189 _106193 k x y) = (term186 _106189 _106193 k x y).
Proof. exact (@lem4410619 _106193 (term179 _106189 _106193 k x y) (term120 _106189 _106193 k x y)). Qed.
Lemma lem4410621 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term187 _106189 _106193 k x y i) = (term177 _106189 _106193 k x y i).
Proof. exact (eq_refl (term187 _106189 _106193 k x y i)). Qed.
Lemma lem4410622 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term188 _106189 _106193 k x y) = (term179 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410621 _106189 _106193 k x y i)). Qed.
Lemma lem4410623 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410624 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term189 _106189 _106193 k x y) = (term180 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410623 _106193) (@lem4410622 _106189 _106193 k x y)). Qed.
Lemma lem4410625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410626 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term190 _106189 _106193 k x y) = (term181 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410625) (@lem4410624 _106189 _106193 k x y)). Qed.
Lemma lem4410627 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term120 _106189 _106193 k x y) = (term120 _106189 _106193 k x y).
Proof. exact (eq_refl (term120 _106189 _106193 k x y)). Qed.
Lemma lem4410628 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term185 _106189 _106193 k x y) = (term182 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410626 _106189 _106193 k x y) (@lem4410627 _106189 _106193 k x y)). Qed.
Lemma lem4410629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410630 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term191 _106189 _106193 k x y) = (term192 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410629) (@lem4410628 _106189 _106193 k x y)). Qed.
Lemma lem4410631 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term187 _106189 _106193 k x y i) = (term177 _106189 _106193 k x y i).
Proof. exact (eq_refl (term187 _106189 _106193 k x y i)). Qed.
Lemma lem4410632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410633 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term193 _106189 _106193 k x y i) = (term194 _106189 _106193 k x y i).
Proof. exact (MK_COMB (@lem4410632) (@lem4410631 _106189 _106193 k x y i)). Qed.
Lemma lem4410634 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term120 _106189 _106193 k x y) = (term120 _106189 _106193 k x y).
Proof. exact (eq_refl (term120 _106189 _106193 k x y)). Qed.
Lemma lem4410635 {_106189 _106193 : Type'} (i : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term195 _106189 _106193 i k x y) = (term196 _106189 _106193 i k x y).
Proof. exact (MK_COMB (@lem4410633 _106189 _106193 k x y i) (@lem4410634 _106189 _106193 k x y)). Qed.
Lemma lem4410636 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term197 _106189 _106193 k x y) = (term198 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410635 _106189 _106193 i k x y)). Qed.
Lemma lem4410637 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410638 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term186 _106189 _106193 k x y) = (term199 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410637 _106193) (@lem4410636 _106189 _106193 k x y)). Qed.
Lemma lem4410639 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((term185 _106189 _106193 k x y) = (term186 _106189 _106193 k x y)) = ((term182 _106189 _106193 k x y) = (term199 _106189 _106193 k x y)).
Proof. exact (MK_COMB (@lem4410630 _106189 _106193 k x y) (@lem4410638 _106189 _106193 k x y)). Qed.
Lemma lem4410640 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term182 _106189 _106193 k x y) = (term199 _106189 _106193 k x y).
Proof. exact (EQ_MP (@lem4410639 _106189 _106193 k x y) (@lem4410620 _106189 _106193 k x y)). Qed.
Lemma lem4410641 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term127 _106189 _106193 k x y) = (term199 _106189 _106193 k x y).
Proof. exact (TRANS (@lem4410616 _106189 _106193 k x y) (@lem4410640 _106189 _106193 k x y)). Qed.
Lemma lem4410642 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term129 _106189 _106193 x y k s) = (term129 _106189 _106193 x y k s).
Proof. exact (eq_refl (term129 _106189 _106193 x y k s)). Qed.
Lemma lem4410643 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term131 _106189 _106193 s k x y) = (term200 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410642 _106189 _106193 x y k s) (@lem4410641 _106189 _106193 k x y)). Qed.
Lemma lem4410645 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4410646 {_106193 : Type'} (P : Prop) (Q : _106193 -> Prop) : (term167 _106193 P Q) = (term168 _106193 P Q).
Proof. exact (@lem4410645 _106193 P Q). Qed.
Lemma lem4410647 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term201 _106189 _106193 s k x y) = (term202 _106189 _106193 s k x y).
Proof. exact (@lem4410646 _106193 (term133 _106189 _106193 x y k s) (term198 _106189 _106193 k x y)). Qed.
Lemma lem4410648 {_106189 _106193 : Type'} (i : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term203 _106189 _106193 k x y i) = (term196 _106189 _106193 i k x y).
Proof. exact (eq_refl (term203 _106189 _106193 k x y i)). Qed.
Lemma lem4410649 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term204 _106189 _106193 k x y) = (term198 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410648 _106189 _106193 i k x y)). Qed.
Lemma lem4410650 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410651 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term205 _106189 _106193 k x y) = (term199 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410650 _106193) (@lem4410649 _106189 _106193 k x y)). Qed.
Lemma lem4410652 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term129 _106189 _106193 x y k s) = (term129 _106189 _106193 x y k s).
Proof. exact (eq_refl (term129 _106189 _106193 x y k s)). Qed.
Lemma lem4410653 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term201 _106189 _106193 s k x y) = (term200 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410652 _106189 _106193 x y k s) (@lem4410651 _106189 _106193 k x y)). Qed.
Lemma lem4410654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410655 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term206 _106189 _106193 s k x y) = (term207 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410654) (@lem4410653 _106189 _106193 s k x y)). Qed.
Lemma lem4410656 {_106189 _106193 : Type'} (i : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term203 _106189 _106193 k x y i) = (term196 _106189 _106193 i k x y).
Proof. exact (eq_refl (term203 _106189 _106193 k x y i)). Qed.
Lemma lem4410657 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term129 _106189 _106193 x y k s) = (term129 _106189 _106193 x y k s).
Proof. exact (eq_refl (term129 _106189 _106193 x y k s)). Qed.
Lemma lem4410658 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term208 _106189 _106193 s k x y i) = (term209 _106189 _106193 s i k x y).
Proof. exact (MK_COMB (@lem4410657 _106189 _106193 x y k s) (@lem4410656 _106189 _106193 i k x y)). Qed.
Lemma lem4410659 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term210 _106189 _106193 s k x y) = (term211 _106189 _106193 s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410658 _106189 _106193 s i k x y)). Qed.
Lemma lem4410660 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410661 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term202 _106189 _106193 s k x y) = (term212 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410660 _106193) (@lem4410659 _106189 _106193 s k x y)). Qed.
Lemma lem4410662 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((term201 _106189 _106193 s k x y) = (term202 _106189 _106193 s k x y)) = ((term200 _106189 _106193 s k x y) = (term212 _106189 _106193 s k x y)).
Proof. exact (MK_COMB (@lem4410655 _106189 _106193 s k x y) (@lem4410661 _106189 _106193 s k x y)). Qed.
Lemma lem4410663 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term200 _106189 _106193 s k x y) = (term212 _106189 _106193 s k x y).
Proof. exact (EQ_MP (@lem4410662 _106189 _106193 s k x y) (@lem4410647 _106189 _106193 s k x y)). Qed.
Lemma lem4410664 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term131 _106189 _106193 s k x y) = (term212 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410643 _106189 _106193 s k x y) (@lem4410663 _106189 _106193 s k x y)). Qed.
Lemma lem4410665 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term141 _106189 _106193 s k x) = (term213 _106189 _106193 s k x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410664 _106189 _106193 s k x y)). Qed.
Lemma lem4410666 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4410667 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term142 _106189 _106193 s k x) = (term214 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410666 _106189 _106193) (@lem4410665 _106189 _106193 s k x)). Qed.
Lemma lem4410668 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term148 _106189 _106193 s k) = (term215 _106189 _106193 s k).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410667 _106189 _106193 s k x)). Qed.
Lemma lem4410669 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4410670 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term149 _106189 _106193 s k) = (term216 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410669 _106189 _106193) (@lem4410668 _106189 _106193 s k)). Qed.
Lemma lem4410671 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term157 _106189 _106193 k) = (term217 _106189 _106193 k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4410670 _106189 _106193 s k)). Qed.
Lemma lem4410672 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189 -> Prop)) = (@ex (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@ex (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4410673 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term158 _106189 _106193 k) = (term218 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410672 _106189 _106193) (@lem4410671 _106189 _106193 k)). Qed.
Lemma lem4410674 {_106189 _106193 : Type'} : (term165 _106189 _106193) = (term219 _106189 _106193).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4410673 _106189 _106193 k)). Qed.
Lemma lem4410675 {_106193 : Type'} : (@ex (_106193 -> Prop)) = (@ex (_106193 -> Prop)).
Proof. exact (eq_refl (@ex (_106193 -> Prop))). Qed.
Lemma lem4410677 {_106189 _106193 : Type'} : (term166 _106189 _106193) = (term220 _106189 _106193).
Proof. exact (MK_COMB (@lem4410675 _106193) (@lem4410674 _106189 _106193)). Qed.
Lemma lem4410678 {_106189 _106193 : Type'} : (term10 _106189 _106193) = (term220 _106189 _106193).
Proof. exact (TRANS (@lem4410435 _106189 _106193) (@lem4410677 _106189 _106193)). Qed.
Lemma lem4410679 {_106189 _106193 : Type'} (h1 : term10 _106189 _106193) : term220 _106189 _106193.
Proof. exact (EQ_MP (@lem4410678 _106189 _106193) (@lem4410340 _106189 _106193 h1)). Qed.
Lemma lem4410688 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term104 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (@lem17362 (@IN _106193 i k) ((x i) = (y i))). Qed.
Lemma lem4410689 {_106193 : Type'} (P : _106193 -> Prop) : (term107 _106193 P) = (term108 _106193 P).
Proof. exact (@lem18392 _106193 P). Qed.
Lemma lem4410690 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term109 _106189 _106193 k x y) = (term110 _106189 _106193 k x y).
Proof. exact (@lem4410689 _106193 (term65 _106189 _106193 k x y)). Qed.
Lemma lem4410691 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term111 _106189 _106193 k x y i) = (term64 _106189 _106193 k x y i).
Proof. exact (eq_refl (term111 _106189 _106193 k x y i)). Qed.
Lemma lem4410692 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4410693 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term112 _106189 _106193 k x y i) = (term104 _106189 _106193 k x y i).
Proof. exact (MK_COMB (@lem4410692) (@lem4410691 _106189 _106193 k x y i)). Qed.
Lemma lem4410694 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term112 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (TRANS (@lem4410693 _106189 _106193 k x y i) (@lem4410688 _106189 _106193 k x y i)). Qed.
Lemma lem4410695 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term113 _106189 _106193 k x y) = (term114 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410694 _106189 _106193 k x y i)). Qed.
Lemma lem4410696 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410697 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term110 _106189 _106193 k x y) = (term115 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410696 _106193) (@lem4410695 _106189 _106193 k x y)). Qed.
Lemma lem4410698 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term109 _106189 _106193 k x y) = (term115 _106189 _106193 k x y).
Proof. exact (TRANS (@lem4410690 _106189 _106193 k x y) (@lem4410697 _106189 _106193 k x y)). Qed.
Lemma lem4410700 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 y k s) = (term221 _106189 _106193 y k s).
Proof. exact (eq_refl (term221 _106189 _106193 y k s)). Qed.
Lemma lem4410701 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term222 _106189 _106193 s k x y) = (term223 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410700 _106189 _106193 y k s) (@lem4410698 _106189 _106193 k x y)). Qed.
Lemma lem4410702 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term224 _106189 _106193 s k x y) = (term222 _106189 _106193 s k x y).
Proof. exact (@lem17045 (term225 _106189 _106193 y k s) (term66 _106189 _106193 k x y)). Qed.
Lemma lem4410703 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term224 _106189 _106193 s k x y) = (term223 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410702 _106189 _106193 s k x y) (@lem4410701 _106189 _106193 s k x y)). Qed.
Lemma lem4410705 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 x k s) = (term221 _106189 _106193 x k s).
Proof. exact (eq_refl (term221 _106189 _106193 x k s)). Qed.
Lemma lem4410706 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term226 _106189 _106193 s k x y) = (term227 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410705 _106189 _106193 x k s) (@lem4410703 _106189 _106193 s k x y)). Qed.
Lemma lem4410707 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term228 _106189 _106193 s k x y) = (term226 _106189 _106193 s k x y).
Proof. exact (@lem17045 (term225 _106189 _106193 x k s) (term68 _106189 _106193 s k x y)). Qed.
Lemma lem4410708 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term228 _106189 _106193 s k x y) = (term227 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410707 _106189 _106193 s k x y) (@lem4410706 _106189 _106193 s k x y)). Qed.
Lemma lem4410709 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4410710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410711 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term229 _106189 _106193 s k x y) = (term230 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410710) (@lem4410708 _106189 _106193 s k x y)). Qed.
Lemma lem4410712 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term231 _106189 _106193 s k x y) = (term232 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410711 _106189 _106193 s k x y) (@lem4410709 _106189 _106193 x y)). Qed.
Lemma lem4410713 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term71 _106189 _106193 s k x y) = (term231 _106189 _106193 s k x y).
Proof. exact (@lem17265 (term69 _106189 _106193 s k x y) (x = y)). Qed.
Lemma lem4410714 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term71 _106189 _106193 s k x y) = (term232 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410713 _106189 _106193 s k x y) (@lem4410712 _106189 _106193 s k x y)). Qed.
Lemma lem4410715 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term72 _106189 _106193 s k x) = (term233 _106189 _106193 s k x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410714 _106189 _106193 s k x y)). Qed.
Lemma lem4410716 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410717 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term73 _106189 _106193 s k x) = (term234 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410716 _106189 _106193) (@lem4410715 _106189 _106193 s k x)). Qed.
Lemma lem4410718 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term74 _106189 _106193 s k) = (term235 _106189 _106193 s k).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410717 _106189 _106193 s k x)). Qed.
Lemma lem4410719 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410720 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term75 _106189 _106193 s k) = (term236 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410719 _106189 _106193) (@lem4410718 _106189 _106193 s k)). Qed.
Lemma lem4410721 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term76 _106189 _106193 k) = (term237 _106189 _106193 k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4410720 _106189 _106193 s k)). Qed.
Lemma lem4410722 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4410723 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term77 _106189 _106193 k) = (term238 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410722 _106189 _106193) (@lem4410721 _106189 _106193 k)). Qed.
Lemma lem4410724 {_106189 _106193 : Type'} : (term78 _106189 _106193) = (term239 _106189 _106193).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4410723 _106189 _106193 k)). Qed.
Lemma lem4410725 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4410726 {_106189 _106193 : Type'} : (term11 _106189 _106193) = (term240 _106189 _106193).
Proof. exact (MK_COMB (@lem4410725 _106193) (@lem4410724 _106189 _106193)). Qed.
Lemma lem4410837 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4410838 {_106193 : Type'} (P : Prop) (Q : _106193 -> Prop) : (term241 _106193 P Q) = (term242 _106193 P Q).
Proof. exact (@lem4410837 _106193 P Q). Qed.
Lemma lem4410839 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term243 _106189 _106193 s k x y) = (term244 _106189 _106193 s k x y).
Proof. exact (@lem4410838 _106193 (term245 _106189 _106193 y k s) (term114 _106189 _106193 k x y)). Qed.
Lemma lem4410840 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term171 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (eq_refl (term171 _106189 _106193 k x y i)). Qed.
Lemma lem4410841 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term172 _106189 _106193 k x y) = (term114 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410840 _106189 _106193 k x y i)). Qed.
Lemma lem4410842 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410843 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term173 _106189 _106193 k x y) = (term115 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4410842 _106193) (@lem4410841 _106189 _106193 k x y)). Qed.
Lemma lem4410844 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 y k s) = (term221 _106189 _106193 y k s).
Proof. exact (eq_refl (term221 _106189 _106193 y k s)). Qed.
Lemma lem4410845 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term243 _106189 _106193 s k x y) = (term223 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410844 _106189 _106193 y k s) (@lem4410843 _106189 _106193 k x y)). Qed.
Lemma lem4410846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410847 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term246 _106189 _106193 s k x y) = (term247 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410846) (@lem4410845 _106189 _106193 s k x y)). Qed.
Lemma lem4410848 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term171 _106189 _106193 k x y i) = (term105 _106189 _106193 k x y i).
Proof. exact (eq_refl (term171 _106189 _106193 k x y i)). Qed.
Lemma lem4410849 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 y k s) = (term221 _106189 _106193 y k s).
Proof. exact (eq_refl (term221 _106189 _106193 y k s)). Qed.
Lemma lem4410850 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term248 _106189 _106193 s k x y i) = (term249 _106189 _106193 s k x y i).
Proof. exact (MK_COMB (@lem4410849 _106189 _106193 y k s) (@lem4410848 _106189 _106193 k x y i)). Qed.
Lemma lem4410851 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term250 _106189 _106193 s k x y) = (term251 _106189 _106193 s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410850 _106189 _106193 s k x y i)). Qed.
Lemma lem4410852 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410853 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term244 _106189 _106193 s k x y) = (term252 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410852 _106193) (@lem4410851 _106189 _106193 s k x y)). Qed.
Lemma lem4410854 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((term243 _106189 _106193 s k x y) = (term244 _106189 _106193 s k x y)) = ((term223 _106189 _106193 s k x y) = (term252 _106189 _106193 s k x y)).
Proof. exact (MK_COMB (@lem4410847 _106189 _106193 s k x y) (@lem4410853 _106189 _106193 s k x y)). Qed.
Lemma lem4410855 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term223 _106189 _106193 s k x y) = (term252 _106189 _106193 s k x y).
Proof. exact (EQ_MP (@lem4410854 _106189 _106193 s k x y) (@lem4410839 _106189 _106193 s k x y)). Qed.
Lemma lem4410856 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 x k s) = (term221 _106189 _106193 x k s).
Proof. exact (eq_refl (term221 _106189 _106193 x k s)). Qed.
Lemma lem4410857 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term227 _106189 _106193 s k x y) = (term253 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410856 _106189 _106193 x k s) (@lem4410855 _106189 _106193 s k x y)). Qed.
Lemma lem4410859 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4410860 {_106193 : Type'} (P : Prop) (Q : _106193 -> Prop) : (term241 _106193 P Q) = (term242 _106193 P Q).
Proof. exact (@lem4410859 _106193 P Q). Qed.
Lemma lem4410861 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term254 _106189 _106193 s k x y) = (term255 _106189 _106193 s k x y).
Proof. exact (@lem4410860 _106193 (term245 _106189 _106193 x k s) (term251 _106189 _106193 s k x y)). Qed.
Lemma lem4410862 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term256 _106189 _106193 s k x y i) = (term249 _106189 _106193 s k x y i).
Proof. exact (eq_refl (term256 _106189 _106193 s k x y i)). Qed.
Lemma lem4410863 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term257 _106189 _106193 s k x y) = (term251 _106189 _106193 s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410862 _106189 _106193 s k x y i)). Qed.
Lemma lem4410864 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410865 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term258 _106189 _106193 s k x y) = (term252 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410864 _106193) (@lem4410863 _106189 _106193 s k x y)). Qed.
Lemma lem4410866 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 x k s) = (term221 _106189 _106193 x k s).
Proof. exact (eq_refl (term221 _106189 _106193 x k s)). Qed.
Lemma lem4410867 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term254 _106189 _106193 s k x y) = (term253 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410866 _106189 _106193 x k s) (@lem4410865 _106189 _106193 s k x y)). Qed.
Lemma lem4410868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410869 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term259 _106189 _106193 s k x y) = (term260 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410868) (@lem4410867 _106189 _106193 s k x y)). Qed.
Lemma lem4410870 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term256 _106189 _106193 s k x y i) = (term249 _106189 _106193 s k x y i).
Proof. exact (eq_refl (term256 _106189 _106193 s k x y i)). Qed.
Lemma lem4410871 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 x k s) = (term221 _106189 _106193 x k s).
Proof. exact (eq_refl (term221 _106189 _106193 x k s)). Qed.
Lemma lem4410872 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term261 _106189 _106193 s k x y i) = (term262 _106189 _106193 s k x y i).
Proof. exact (MK_COMB (@lem4410871 _106189 _106193 x k s) (@lem4410870 _106189 _106193 s k x y i)). Qed.
Lemma lem4410873 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term263 _106189 _106193 s k x y) = (term264 _106189 _106193 s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410872 _106189 _106193 s k x y i)). Qed.
Lemma lem4410874 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410875 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term255 _106189 _106193 s k x y) = (term265 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410874 _106193) (@lem4410873 _106189 _106193 s k x y)). Qed.
Lemma lem4410876 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((term254 _106189 _106193 s k x y) = (term255 _106189 _106193 s k x y)) = ((term253 _106189 _106193 s k x y) = (term265 _106189 _106193 s k x y)).
Proof. exact (MK_COMB (@lem4410869 _106189 _106193 s k x y) (@lem4410875 _106189 _106193 s k x y)). Qed.
Lemma lem4410877 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term253 _106189 _106193 s k x y) = (term265 _106189 _106193 s k x y).
Proof. exact (EQ_MP (@lem4410876 _106189 _106193 s k x y) (@lem4410861 _106189 _106193 s k x y)). Qed.
Lemma lem4410878 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term227 _106189 _106193 s k x y) = (term265 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410857 _106189 _106193 s k x y) (@lem4410877 _106189 _106193 s k x y)). Qed.
Lemma lem4410879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410880 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term230 _106189 _106193 s k x y) = (term266 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410879) (@lem4410878 _106189 _106193 s k x y)). Qed.
Lemma lem4410881 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4410882 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term232 _106189 _106193 s k x y) = (term267 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410880 _106189 _106193 s k x y) (@lem4410881 _106189 _106193 x y)). Qed.
Lemma lem4410884 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4410885 {_106193 : Type'} (P : _106193 -> Prop) (Q : Prop) : (term183 _106193 P Q) = (term184 _106193 P Q).
Proof. exact (@lem4410884 _106193 P Q). Qed.
Lemma lem4410886 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term268 _106189 _106193 s k x y) = (term269 _106189 _106193 s k x y).
Proof. exact (@lem4410885 _106193 (term264 _106189 _106193 s k x y) (x = y)). Qed.
Lemma lem4410887 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term270 _106189 _106193 s k x y i) = (term262 _106189 _106193 s k x y i).
Proof. exact (eq_refl (term270 _106189 _106193 s k x y i)). Qed.
Lemma lem4410888 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term271 _106189 _106193 s k x y) = (term264 _106189 _106193 s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410887 _106189 _106193 s k x y i)). Qed.
Lemma lem4410889 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410890 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term272 _106189 _106193 s k x y) = (term265 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410889 _106193) (@lem4410888 _106189 _106193 s k x y)). Qed.
Lemma lem4410891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410892 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term273 _106189 _106193 s k x y) = (term266 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410891) (@lem4410890 _106189 _106193 s k x y)). Qed.
Lemma lem4410893 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4410894 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term268 _106189 _106193 s k x y) = (term267 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410892 _106189 _106193 s k x y) (@lem4410893 _106189 _106193 x y)). Qed.
Lemma lem4410895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410896 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term274 _106189 _106193 s k x y) = (term275 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410895) (@lem4410894 _106189 _106193 s k x y)). Qed.
Lemma lem4410897 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term270 _106189 _106193 s k x y i) = (term262 _106189 _106193 s k x y i).
Proof. exact (eq_refl (term270 _106189 _106193 s k x y i)). Qed.
Lemma lem4410898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4410899 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term276 _106189 _106193 s k x y i) = (term277 _106189 _106193 s k x y i).
Proof. exact (MK_COMB (@lem4410898) (@lem4410897 _106189 _106193 s k x y i)). Qed.
Lemma lem4410900 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4410901 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term278 _106189 _106193 s k i x y) = (term279 _106189 _106193 s k i x y).
Proof. exact (MK_COMB (@lem4410899 _106189 _106193 s k x y i) (@lem4410900 _106189 _106193 x y)). Qed.
Lemma lem4410902 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term280 _106189 _106193 s k x y) = (term281 _106189 _106193 s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410901 _106189 _106193 s k i x y)). Qed.
Lemma lem4410903 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410904 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term269 _106189 _106193 s k x y) = (term282 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410903 _106193) (@lem4410902 _106189 _106193 s k x y)). Qed.
Lemma lem4410905 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((term268 _106189 _106193 s k x y) = (term269 _106189 _106193 s k x y)) = ((term267 _106189 _106193 s k x y) = (term282 _106189 _106193 s k x y)).
Proof. exact (MK_COMB (@lem4410896 _106189 _106193 s k x y) (@lem4410904 _106189 _106193 s k x y)). Qed.
Lemma lem4410906 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term267 _106189 _106193 s k x y) = (term282 _106189 _106193 s k x y).
Proof. exact (EQ_MP (@lem4410905 _106189 _106193 s k x y) (@lem4410886 _106189 _106193 s k x y)). Qed.
Lemma lem4410907 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term232 _106189 _106193 s k x y) = (term282 _106189 _106193 s k x y).
Proof. exact (TRANS (@lem4410882 _106189 _106193 s k x y) (@lem4410906 _106189 _106193 s k x y)). Qed.
Lemma lem4410908 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term233 _106189 _106193 s k x) = (term283 _106189 _106193 s k x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410907 _106189 _106193 s k x y)). Qed.
Lemma lem4410909 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410910 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term234 _106189 _106193 s k x) = (term284 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410909 _106189 _106193) (@lem4410908 _106189 _106193 s k x)). Qed.
Lemma lem4410912 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4410913 {_106189 _106193 : Type'} (P : type799 _106189 _106193) : (term287 _106189 _106193 P) = (term288 _106189 _106193 P).
Proof. exact (@lem4410912 (_106193 -> _106189) _106193 P). Qed.
Lemma lem4410914 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term289 _106189 _106193 s k x) = (term290 _106189 _106193 s k x).
Proof. exact (@lem4410913 _106189 _106193 (term291 _106189 _106193 s k x)). Qed.
Lemma lem4410915 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term292 _106189 _106193 s k x y) = (term281 _106189 _106193 s k x y).
Proof. exact (eq_refl (term292 _106189 _106193 s k x y)). Qed.
Lemma lem4410916 {_106193 : Type'} (i : _106193) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4410917 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term293 _106189 _106193 s k x y i) = (term294 _106189 _106193 s k x y i).
Proof. exact (MK_COMB (@lem4410915 _106189 _106193 s k x y) (@lem4410916 _106193 i)). Qed.
Lemma lem4410918 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term294 _106189 _106193 s k x y i) = (term279 _106189 _106193 s k i x y).
Proof. exact (eq_refl (term294 _106189 _106193 s k x y i)). Qed.
Lemma lem4410919 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term293 _106189 _106193 s k x y i) = (term279 _106189 _106193 s k i x y).
Proof. exact (TRANS (@lem4410917 _106189 _106193 s k x y i) (@lem4410918 _106189 _106193 s k i x y)). Qed.
Lemma lem4410920 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term295 _106189 _106193 s k x y) = (term281 _106189 _106193 s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4410919 _106189 _106193 s k i x y)). Qed.
Lemma lem4410921 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4410922 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term296 _106189 _106193 s k x y) = (term282 _106189 _106193 s k x y).
Proof. exact (MK_COMB (@lem4410921 _106193) (@lem4410920 _106189 _106193 s k x y)). Qed.
Lemma lem4410923 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term297 _106189 _106193 s k x) = (term283 _106189 _106193 s k x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410922 _106189 _106193 s k x y)). Qed.
Lemma lem4410924 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410925 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term289 _106189 _106193 s k x) = (term284 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410924 _106189 _106193) (@lem4410923 _106189 _106193 s k x)). Qed.
Lemma lem4410926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410927 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term298 _106189 _106193 s k x) = (term299 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410926) (@lem4410925 _106189 _106193 s k x)). Qed.
Lemma lem4410928 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term292 _106189 _106193 s k x y) = (term281 _106189 _106193 s k x y).
Proof. exact (eq_refl (term292 _106189 _106193 s k x y)). Qed.
Lemma lem4410929 {_106189 _106193 : Type'} (i : type803 _106189 _106193) (y : _106193 -> _106189) : (i y) = (i y).
Proof. exact (eq_refl (i y)). Qed.
Lemma lem4410930 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (i : type803 _106189 _106193) (y : _106193 -> _106189) : (term300 _106189 _106193 s k x i y) = (term301 _106189 _106193 s k x i y).
Proof. exact (MK_COMB (@lem4410928 _106189 _106193 s k x y) (@lem4410929 _106189 _106193 i y)). Qed.
Lemma lem4410931 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type803 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term301 _106189 _106193 s k x i y) = (term302 _106189 _106193 s k i x y).
Proof. exact (eq_refl (term301 _106189 _106193 s k x i y)). Qed.
Lemma lem4410932 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type803 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term300 _106189 _106193 s k x i y) = (term302 _106189 _106193 s k i x y).
Proof. exact (TRANS (@lem4410930 _106189 _106193 s k x i y) (@lem4410931 _106189 _106193 s k i x y)). Qed.
Lemma lem4410933 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type803 _106189 _106193) (x : _106193 -> _106189) : (term303 _106189 _106193 s k x i) = (term304 _106189 _106193 s k i x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4410932 _106189 _106193 s k i x y)). Qed.
Lemma lem4410934 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410935 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type803 _106189 _106193) (x : _106193 -> _106189) : (term305 _106189 _106193 s k x i) = (term306 _106189 _106193 s k i x).
Proof. exact (MK_COMB (@lem4410934 _106189 _106193) (@lem4410933 _106189 _106193 s k i x)). Qed.
Lemma lem4410936 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term307 _106189 _106193 s k x) = (term308 _106189 _106193 s k x).
Proof. exact (fun_ext (fun i : type803 _106189 _106193 => @lem4410935 _106189 _106193 s k i x)). Qed.
Lemma lem4410937 {_106189 _106193 : Type'} : (@ex ((_106193 -> _106189) -> _106193)) = (@ex ((_106193 -> _106189) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> _106189) -> _106193))). Qed.
Lemma lem4410938 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term290 _106189 _106193 s k x) = (term309 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410937 _106189 _106193) (@lem4410936 _106189 _106193 s k x)). Qed.
Lemma lem4410939 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : ((term289 _106189 _106193 s k x) = (term290 _106189 _106193 s k x)) = ((term284 _106189 _106193 s k x) = (term309 _106189 _106193 s k x)).
Proof. exact (MK_COMB (@lem4410927 _106189 _106193 s k x) (@lem4410938 _106189 _106193 s k x)). Qed.
Lemma lem4410940 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term284 _106189 _106193 s k x) = (term309 _106189 _106193 s k x).
Proof. exact (EQ_MP (@lem4410939 _106189 _106193 s k x) (@lem4410914 _106189 _106193 s k x)). Qed.
Lemma lem4410941 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term234 _106189 _106193 s k x) = (term309 _106189 _106193 s k x).
Proof. exact (TRANS (@lem4410910 _106189 _106193 s k x) (@lem4410940 _106189 _106193 s k x)). Qed.
Lemma lem4410942 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term235 _106189 _106193 s k) = (term310 _106189 _106193 s k).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410941 _106189 _106193 s k x)). Qed.
Lemma lem4410943 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410944 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term236 _106189 _106193 s k) = (term311 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410943 _106189 _106193) (@lem4410942 _106189 _106193 s k)). Qed.
Lemma lem4410946 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4410947 {_106189 _106193 : Type'} (P : type772 _106189 _106193) : (term312 _106189 _106193 P) = (term313 _106189 _106193 P).
Proof. exact (@lem4410946 (_106193 -> _106189) (type803 _106189 _106193) P). Qed.
Lemma lem4410948 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term314 _106189 _106193 s k) = (term315 _106189 _106193 s k).
Proof. exact (@lem4410947 _106189 _106193 (term316 _106189 _106193 s k)). Qed.
Lemma lem4410949 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term317 _106189 _106193 s k x) = (term308 _106189 _106193 s k x).
Proof. exact (eq_refl (term317 _106189 _106193 s k x)). Qed.
Lemma lem4410950 {_106189 _106193 : Type'} (i : type803 _106189 _106193) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4410951 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (i : type803 _106189 _106193) : (term318 _106189 _106193 s k x i) = (term319 _106189 _106193 s k x i).
Proof. exact (MK_COMB (@lem4410949 _106189 _106193 s k x) (@lem4410950 _106189 _106193 i)). Qed.
Lemma lem4410952 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type803 _106189 _106193) (x : _106193 -> _106189) : (term319 _106189 _106193 s k x i) = (term306 _106189 _106193 s k i x).
Proof. exact (eq_refl (term319 _106189 _106193 s k x i)). Qed.
Lemma lem4410953 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type803 _106189 _106193) (x : _106193 -> _106189) : (term318 _106189 _106193 s k x i) = (term306 _106189 _106193 s k i x).
Proof. exact (TRANS (@lem4410951 _106189 _106193 s k x i) (@lem4410952 _106189 _106193 s k i x)). Qed.
Lemma lem4410954 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term320 _106189 _106193 s k x) = (term308 _106189 _106193 s k x).
Proof. exact (fun_ext (fun i : type803 _106189 _106193 => @lem4410953 _106189 _106193 s k i x)). Qed.
Lemma lem4410955 {_106189 _106193 : Type'} : (@ex ((_106193 -> _106189) -> _106193)) = (@ex ((_106193 -> _106189) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> _106189) -> _106193))). Qed.
Lemma lem4410956 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term321 _106189 _106193 s k x) = (term309 _106189 _106193 s k x).
Proof. exact (MK_COMB (@lem4410955 _106189 _106193) (@lem4410954 _106189 _106193 s k x)). Qed.
Lemma lem4410957 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term322 _106189 _106193 s k) = (term310 _106189 _106193 s k).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410956 _106189 _106193 s k x)). Qed.
Lemma lem4410958 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410959 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term314 _106189 _106193 s k) = (term311 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410958 _106189 _106193) (@lem4410957 _106189 _106193 s k)). Qed.
Lemma lem4410960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410961 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term323 _106189 _106193 s k) = (term324 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410960) (@lem4410959 _106189 _106193 s k)). Qed.
Lemma lem4410962 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) : (term317 _106189 _106193 s k x) = (term308 _106189 _106193 s k x).
Proof. exact (eq_refl (term317 _106189 _106193 s k x)). Qed.
Lemma lem4410963 {_106189 _106193 : Type'} (i : type785 _106189 _106193) (x : _106193 -> _106189) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem4410964 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) (x : _106193 -> _106189) : (term325 _106189 _106193 s k i x) = (term326 _106189 _106193 s k i x).
Proof. exact (MK_COMB (@lem4410962 _106189 _106193 s k x) (@lem4410963 _106189 _106193 i x)). Qed.
Lemma lem4410965 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) (x : _106193 -> _106189) : (term326 _106189 _106193 s k i x) = (term327 _106189 _106193 s k i x).
Proof. exact (eq_refl (term326 _106189 _106193 s k i x)). Qed.
Lemma lem4410966 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) (x : _106193 -> _106189) : (term325 _106189 _106193 s k i x) = (term327 _106189 _106193 s k i x).
Proof. exact (TRANS (@lem4410964 _106189 _106193 s k i x) (@lem4410965 _106189 _106193 s k i x)). Qed.
Lemma lem4410967 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) : (term328 _106189 _106193 s k i) = (term329 _106189 _106193 s k i).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4410966 _106189 _106193 s k i x)). Qed.
Lemma lem4410968 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4410969 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) : (term330 _106189 _106193 s k i) = (term331 _106189 _106193 s k i).
Proof. exact (MK_COMB (@lem4410968 _106189 _106193) (@lem4410967 _106189 _106193 s k i)). Qed.
Lemma lem4410970 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term332 _106189 _106193 s k) = (term333 _106189 _106193 s k).
Proof. exact (fun_ext (fun i : type785 _106189 _106193 => @lem4410969 _106189 _106193 s k i)). Qed.
Lemma lem4410971 {_106189 _106193 : Type'} : (@ex ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193)) = (@ex ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193))). Qed.
Lemma lem4410972 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term315 _106189 _106193 s k) = (term334 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410971 _106189 _106193) (@lem4410970 _106189 _106193 s k)). Qed.
Lemma lem4410973 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : ((term314 _106189 _106193 s k) = (term315 _106189 _106193 s k)) = ((term311 _106189 _106193 s k) = (term334 _106189 _106193 s k)).
Proof. exact (MK_COMB (@lem4410961 _106189 _106193 s k) (@lem4410972 _106189 _106193 s k)). Qed.
Lemma lem4410974 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term311 _106189 _106193 s k) = (term334 _106189 _106193 s k).
Proof. exact (EQ_MP (@lem4410973 _106189 _106193 s k) (@lem4410948 _106189 _106193 s k)). Qed.
Lemma lem4410975 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term236 _106189 _106193 s k) = (term334 _106189 _106193 s k).
Proof. exact (TRANS (@lem4410944 _106189 _106193 s k) (@lem4410974 _106189 _106193 s k)). Qed.
Lemma lem4410976 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term237 _106189 _106193 k) = (term335 _106189 _106193 k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4410975 _106189 _106193 s k)). Qed.
Lemma lem4410977 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4410978 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term238 _106189 _106193 k) = (term336 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410977 _106189 _106193) (@lem4410976 _106189 _106193 k)). Qed.
Lemma lem4410980 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4410981 {_106189 _106193 : Type'} (P : type729 _106189 _106193) : (term337 _106189 _106193 P) = (term338 _106189 _106193 P).
Proof. exact (@lem4410980 (type1470 _106189 _106193) (type785 _106189 _106193) P). Qed.
Lemma lem4410982 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term339 _106189 _106193 k) = (term340 _106189 _106193 k).
Proof. exact (@lem4410981 _106189 _106193 (term341 _106189 _106193 k)). Qed.
Lemma lem4410983 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term342 _106189 _106193 k s) = (term333 _106189 _106193 s k).
Proof. exact (eq_refl (term342 _106189 _106193 k s)). Qed.
Lemma lem4410984 {_106189 _106193 : Type'} (i : type785 _106189 _106193) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4410985 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) : (term343 _106189 _106193 k s i) = (term344 _106189 _106193 s k i).
Proof. exact (MK_COMB (@lem4410983 _106189 _106193 s k) (@lem4410984 _106189 _106193 i)). Qed.
Lemma lem4410986 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) : (term344 _106189 _106193 s k i) = (term331 _106189 _106193 s k i).
Proof. exact (eq_refl (term344 _106189 _106193 s k i)). Qed.
Lemma lem4410987 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (i : type785 _106189 _106193) : (term343 _106189 _106193 k s i) = (term331 _106189 _106193 s k i).
Proof. exact (TRANS (@lem4410985 _106189 _106193 s k i) (@lem4410986 _106189 _106193 s k i)). Qed.
Lemma lem4410988 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term345 _106189 _106193 k s) = (term333 _106189 _106193 s k).
Proof. exact (fun_ext (fun i : type785 _106189 _106193 => @lem4410987 _106189 _106193 s k i)). Qed.
Lemma lem4410989 {_106189 _106193 : Type'} : (@ex ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193)) = (@ex ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193))). Qed.
Lemma lem4410990 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term346 _106189 _106193 k s) = (term334 _106189 _106193 s k).
Proof. exact (MK_COMB (@lem4410989 _106189 _106193) (@lem4410988 _106189 _106193 s k)). Qed.
Lemma lem4410991 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term347 _106189 _106193 k) = (term335 _106189 _106193 k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4410990 _106189 _106193 s k)). Qed.
Lemma lem4410992 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4410993 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term339 _106189 _106193 k) = (term336 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410992 _106189 _106193) (@lem4410991 _106189 _106193 k)). Qed.
Lemma lem4410994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4410995 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term348 _106189 _106193 k) = (term349 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4410994) (@lem4410993 _106189 _106193 k)). Qed.
Lemma lem4410996 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) : (term342 _106189 _106193 k s) = (term333 _106189 _106193 s k).
Proof. exact (eq_refl (term342 _106189 _106193 k s)). Qed.
Lemma lem4410997 {_106189 _106193 : Type'} (i : type733 _106189 _106193) (s : type1470 _106189 _106193) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem4410998 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) (s : type1470 _106189 _106193) : (term350 _106189 _106193 k i s) = (term351 _106189 _106193 k i s).
Proof. exact (MK_COMB (@lem4410996 _106189 _106193 s k) (@lem4410997 _106189 _106193 i s)). Qed.
Lemma lem4410999 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) (s : type1470 _106189 _106193) : (term351 _106189 _106193 k i s) = (term352 _106189 _106193 k i s).
Proof. exact (eq_refl (term351 _106189 _106193 k i s)). Qed.
Lemma lem4411000 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) (s : type1470 _106189 _106193) : (term350 _106189 _106193 k i s) = (term352 _106189 _106193 k i s).
Proof. exact (TRANS (@lem4410998 _106189 _106193 k i s) (@lem4410999 _106189 _106193 k i s)). Qed.
Lemma lem4411001 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) : (term353 _106189 _106193 k i) = (term354 _106189 _106193 k i).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4411000 _106189 _106193 k i s)). Qed.
Lemma lem4411002 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4411003 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) : (term355 _106189 _106193 k i) = (term356 _106189 _106193 k i).
Proof. exact (MK_COMB (@lem4411002 _106189 _106193) (@lem4411001 _106189 _106193 k i)). Qed.
Lemma lem4411004 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term357 _106189 _106193 k) = (term358 _106189 _106193 k).
Proof. exact (fun_ext (fun i : type733 _106189 _106193 => @lem4411003 _106189 _106193 k i)). Qed.
Lemma lem4411005 {_106189 _106193 : Type'} : (@ex ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193)) = (@ex ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193))). Qed.
Lemma lem4411006 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term340 _106189 _106193 k) = (term359 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4411005 _106189 _106193) (@lem4411004 _106189 _106193 k)). Qed.
Lemma lem4411007 {_106189 _106193 : Type'} (k : _106193 -> Prop) : ((term339 _106189 _106193 k) = (term340 _106189 _106193 k)) = ((term336 _106189 _106193 k) = (term359 _106189 _106193 k)).
Proof. exact (MK_COMB (@lem4410995 _106189 _106193 k) (@lem4411006 _106189 _106193 k)). Qed.
Lemma lem4411008 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term336 _106189 _106193 k) = (term359 _106189 _106193 k).
Proof. exact (EQ_MP (@lem4411007 _106189 _106193 k) (@lem4410982 _106189 _106193 k)). Qed.
Lemma lem4411009 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term238 _106189 _106193 k) = (term359 _106189 _106193 k).
Proof. exact (TRANS (@lem4410978 _106189 _106193 k) (@lem4411008 _106189 _106193 k)). Qed.
Lemma lem4411010 {_106189 _106193 : Type'} : (term239 _106189 _106193) = (term360 _106189 _106193).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4411009 _106189 _106193 k)). Qed.
Lemma lem4411011 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4411012 {_106189 _106193 : Type'} : (term240 _106189 _106193) = (term361 _106189 _106193).
Proof. exact (MK_COMB (@lem4411011 _106193) (@lem4411010 _106189 _106193)). Qed.
Lemma lem4411014 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411015 {_106189 _106193 : Type'} (P : type824 _106189 _106193) : (term362 _106189 _106193 P) = (term363 _106189 _106193 P).
Proof. exact (@lem4411014 (_106193 -> Prop) (type733 _106189 _106193) P). Qed.
Lemma lem4411016 {_106189 _106193 : Type'} : (term364 _106189 _106193) = (term365 _106189 _106193).
Proof. exact (@lem4411015 _106189 _106193 (term366 _106189 _106193)). Qed.
Lemma lem4411017 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term367 _106189 _106193 k) = (term358 _106189 _106193 k).
Proof. exact (eq_refl (term367 _106189 _106193 k)). Qed.
Lemma lem4411018 {_106189 _106193 : Type'} (i : type733 _106189 _106193) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411019 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) : (term368 _106189 _106193 k i) = (term369 _106189 _106193 k i).
Proof. exact (MK_COMB (@lem4411017 _106189 _106193 k) (@lem4411018 _106189 _106193 i)). Qed.
Lemma lem4411020 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) : (term369 _106189 _106193 k i) = (term356 _106189 _106193 k i).
Proof. exact (eq_refl (term369 _106189 _106193 k i)). Qed.
Lemma lem4411021 {_106189 _106193 : Type'} (k : _106193 -> Prop) (i : type733 _106189 _106193) : (term368 _106189 _106193 k i) = (term356 _106189 _106193 k i).
Proof. exact (TRANS (@lem4411019 _106189 _106193 k i) (@lem4411020 _106189 _106193 k i)). Qed.
Lemma lem4411022 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term370 _106189 _106193 k) = (term358 _106189 _106193 k).
Proof. exact (fun_ext (fun i : type733 _106189 _106193 => @lem4411021 _106189 _106193 k i)). Qed.
Lemma lem4411023 {_106189 _106193 : Type'} : (@ex ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193)) = (@ex ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193))). Qed.
Lemma lem4411024 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term371 _106189 _106193 k) = (term359 _106189 _106193 k).
Proof. exact (MK_COMB (@lem4411023 _106189 _106193) (@lem4411022 _106189 _106193 k)). Qed.
Lemma lem4411025 {_106189 _106193 : Type'} : (term372 _106189 _106193) = (term360 _106189 _106193).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4411024 _106189 _106193 k)). Qed.
Lemma lem4411026 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4411027 {_106189 _106193 : Type'} : (term364 _106189 _106193) = (term361 _106189 _106193).
Proof. exact (MK_COMB (@lem4411026 _106193) (@lem4411025 _106189 _106193)). Qed.
Lemma lem4411028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411029 {_106189 _106193 : Type'} : (term373 _106189 _106193) = (term374 _106189 _106193).
Proof. exact (MK_COMB (@lem4411028) (@lem4411027 _106189 _106193)). Qed.
Lemma lem4411030 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (term367 _106189 _106193 k) = (term358 _106189 _106193 k).
Proof. exact (eq_refl (term367 _106189 _106193 k)). Qed.
Lemma lem4411031 {_106189 _106193 : Type'} (i : type844 _106189 _106193) (k : _106193 -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem4411032 {_106189 _106193 : Type'} (i : type844 _106189 _106193) (k : _106193 -> Prop) : (term375 _106189 _106193 i k) = (term376 _106189 _106193 i k).
Proof. exact (MK_COMB (@lem4411030 _106189 _106193 k) (@lem4411031 _106189 _106193 i k)). Qed.
Lemma lem4411033 {_106189 _106193 : Type'} (i : type844 _106189 _106193) (k : _106193 -> Prop) : (term376 _106189 _106193 i k) = (term377 _106189 _106193 i k).
Proof. exact (eq_refl (term376 _106189 _106193 i k)). Qed.
Lemma lem4411034 {_106189 _106193 : Type'} (i : type844 _106189 _106193) (k : _106193 -> Prop) : (term375 _106189 _106193 i k) = (term377 _106189 _106193 i k).
Proof. exact (TRANS (@lem4411032 _106189 _106193 i k) (@lem4411033 _106189 _106193 i k)). Qed.
Lemma lem4411035 {_106189 _106193 : Type'} (i : type844 _106189 _106193) : (term378 _106189 _106193 i) = (term379 _106189 _106193 i).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4411034 _106189 _106193 i k)). Qed.
Lemma lem4411036 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4411037 {_106189 _106193 : Type'} (i : type844 _106189 _106193) : (term380 _106189 _106193 i) = (term381 _106189 _106193 i).
Proof. exact (MK_COMB (@lem4411036 _106193) (@lem4411035 _106189 _106193 i)). Qed.
Lemma lem4411038 {_106189 _106193 : Type'} : (term382 _106189 _106193) = (term383 _106189 _106193).
Proof. exact (fun_ext (fun i : type844 _106189 _106193 => @lem4411037 _106189 _106193 i)). Qed.
Lemma lem4411039 {_106189 _106193 : Type'} : (@ex ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193)) = (@ex ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193))). Qed.
Lemma lem4411040 {_106189 _106193 : Type'} : (term365 _106189 _106193) = (term384 _106189 _106193).
Proof. exact (MK_COMB (@lem4411039 _106189 _106193) (@lem4411038 _106189 _106193)). Qed.
Lemma lem4411041 {_106189 _106193 : Type'} : ((term364 _106189 _106193) = (term365 _106189 _106193)) = ((term361 _106189 _106193) = (term384 _106189 _106193)).
Proof. exact (MK_COMB (@lem4411029 _106189 _106193) (@lem4411040 _106189 _106193)). Qed.
Lemma lem4411042 {_106189 _106193 : Type'} : (term361 _106189 _106193) = (term384 _106189 _106193).
Proof. exact (EQ_MP (@lem4411041 _106189 _106193) (@lem4411016 _106189 _106193)). Qed.
Lemma lem4411044 {_106189 _106193 : Type'} : (term240 _106189 _106193) = (term384 _106189 _106193).
Proof. exact (TRANS (@lem4411012 _106189 _106193) (@lem4411042 _106189 _106193)). Qed.
Lemma lem4411045 {_106189 _106193 : Type'} : (term11 _106189 _106193) = (term384 _106189 _106193).
Proof. exact (TRANS (@lem4410726 _106189 _106193) (@lem4411044 _106189 _106193)). Qed.
Lemma lem4411046 {_106189 _106193 : Type'} (h1 : term11 _106189 _106193) : term384 _106189 _106193.
Proof. exact (EQ_MP (@lem4411045 _106189 _106193) (@lem4410341 _106189 _106193 h1)). Qed.
Lemma lem4411055 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term385 _106193 A k x y i) = (term386 _106193 A k x y i).
Proof. exact (@lem17362 (@IN _106193 i k) ((x i) = (y i))). Qed.
Lemma lem4411056 {_106193 : Type'} (P : _106193 -> Prop) : (term107 _106193 P) = (term108 _106193 P).
Proof. exact (@lem18392 _106193 P). Qed.
Lemma lem4411057 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term387 _106193 A k x y) = (term388 _106193 A k x y).
Proof. exact (@lem4411056 _106193 (term80 _106193 A k x y)). Qed.
Lemma lem4411058 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term389 _106193 A k x y i) = (term79 _106193 A k x y i).
Proof. exact (eq_refl (term389 _106193 A k x y i)). Qed.
Lemma lem4411059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4411060 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term390 _106193 A k x y i) = (term385 _106193 A k x y i).
Proof. exact (MK_COMB (@lem4411059) (@lem4411058 _106193 A k x y i)). Qed.
Lemma lem4411061 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term390 _106193 A k x y i) = (term386 _106193 A k x y i).
Proof. exact (TRANS (@lem4411060 _106193 A k x y i) (@lem4411055 _106193 A k x y i)). Qed.
Lemma lem4411062 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term391 _106193 A k x y) = (term392 _106193 A k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411061 _106193 A k x y i)). Qed.
Lemma lem4411063 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411064 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term388 _106193 A k x y) = (term393 _106193 A k x y).
Proof. exact (MK_COMB (@lem4411063 _106193) (@lem4411062 _106193 A k x y)). Qed.
Lemma lem4411065 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term387 _106193 A k x y) = (term393 _106193 A k x y).
Proof. exact (TRANS (@lem4411057 _106193 A k x y) (@lem4411064 _106193 A k x y)). Qed.
Lemma lem4411067 {_106193 A : Type'} (y : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term394 _106193 A y k s) = (term394 _106193 A y k s).
Proof. exact (eq_refl (term394 _106193 A y k s)). Qed.
Lemma lem4411068 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term395 _106193 A s k x y) = (term396 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411067 _106193 A y k s) (@lem4411065 _106193 A k x y)). Qed.
Lemma lem4411069 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term397 _106193 A s k x y) = (term395 _106193 A s k x y).
Proof. exact (@lem17045 (term398 _106193 A y k s) (term81 _106193 A k x y)). Qed.
Lemma lem4411070 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term397 _106193 A s k x y) = (term396 _106193 A s k x y).
Proof. exact (TRANS (@lem4411069 _106193 A s k x y) (@lem4411068 _106193 A s k x y)). Qed.
Lemma lem4411072 {_106193 A : Type'} (x : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term394 _106193 A x k s) = (term394 _106193 A x k s).
Proof. exact (eq_refl (term394 _106193 A x k s)). Qed.
Lemma lem4411073 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term399 _106193 A s k x y) = (term400 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411072 _106193 A x k s) (@lem4411070 _106193 A s k x y)). Qed.
Lemma lem4411074 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term401 _106193 A s k x y) = (term399 _106193 A s k x y).
Proof. exact (@lem17045 (term398 _106193 A x k s) (term83 _106193 A s k x y)). Qed.
Lemma lem4411075 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term401 _106193 A s k x y) = (term400 _106193 A s k x y).
Proof. exact (TRANS (@lem4411074 _106193 A s k x y) (@lem4411073 _106193 A s k x y)). Qed.
Lemma lem4411076 {_106193 A : Type'} (x : _106193 -> A) (y : _106193 -> A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411078 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term402 _106193 A s k x y) = (term403 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411077) (@lem4411075 _106193 A s k x y)). Qed.
Lemma lem4411079 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term404 _106193 A s k x y) = (term405 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411078 _106193 A s k x y) (@lem4411076 _106193 A x y)). Qed.
Lemma lem4411080 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term86 _106193 A s k x y) = (term404 _106193 A s k x y).
Proof. exact (@lem17265 (term84 _106193 A s k x y) (x = y)). Qed.
Lemma lem4411081 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term86 _106193 A s k x y) = (term405 _106193 A s k x y).
Proof. exact (TRANS (@lem4411080 _106193 A s k x y) (@lem4411079 _106193 A s k x y)). Qed.
Lemma lem4411082 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term87 _106193 A s k x) = (term406 _106193 A s k x).
Proof. exact (fun_ext (fun y : _106193 -> A => @lem4411081 _106193 A s k x y)). Qed.
Lemma lem4411083 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411084 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term88 _106193 A s k x) = (term407 _106193 A s k x).
Proof. exact (MK_COMB (@lem4411083 _106193 A) (@lem4411082 _106193 A s k x)). Qed.
Lemma lem4411085 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term89 _106193 A s k) = (term408 _106193 A s k).
Proof. exact (fun_ext (fun x : _106193 -> A => @lem4411084 _106193 A s k x)). Qed.
Lemma lem4411086 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411087 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term90 _106193 A s k) = (term409 _106193 A s k).
Proof. exact (MK_COMB (@lem4411086 _106193 A) (@lem4411085 _106193 A s k)). Qed.
Lemma lem4411088 {_106193 A : Type'} (k : _106193 -> Prop) : (term91 _106193 A k) = (term410 _106193 A k).
Proof. exact (fun_ext (fun s : type1413 _106193 A => @lem4411087 _106193 A s k)). Qed.
Lemma lem4411089 {_106193 A : Type'} : (@all (_106193 -> A -> Prop)) = (@all (_106193 -> A -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> A -> Prop))). Qed.
Lemma lem4411090 {_106193 A : Type'} (k : _106193 -> Prop) : (term92 _106193 A k) = (term411 _106193 A k).
Proof. exact (MK_COMB (@lem4411089 _106193 A) (@lem4411088 _106193 A k)). Qed.
Lemma lem4411091 {_106193 A : Type'} : (term93 _106193 A) = (term412 _106193 A).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4411090 _106193 A k)). Qed.
Lemma lem4411092 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4411093 {_106193 A : Type'} : (term13 _106193 A) = (term413 _106193 A).
Proof. exact (MK_COMB (@lem4411092 _106193) (@lem4411091 _106193 A)). Qed.
Lemma lem4411204 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4411205 {_106193 : Type'} (P : Prop) (Q : _106193 -> Prop) : (term241 _106193 P Q) = (term242 _106193 P Q).
Proof. exact (@lem4411204 _106193 P Q). Qed.
Lemma lem4411206 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term414 _106193 A s k x y) = (term415 _106193 A s k x y).
Proof. exact (@lem4411205 _106193 (term416 _106193 A y k s) (term392 _106193 A k x y)). Qed.
Lemma lem4411207 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term417 _106193 A k x y i) = (term386 _106193 A k x y i).
Proof. exact (eq_refl (term417 _106193 A k x y i)). Qed.
Lemma lem4411208 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term418 _106193 A k x y) = (term392 _106193 A k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411207 _106193 A k x y i)). Qed.
Lemma lem4411209 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411210 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term419 _106193 A k x y) = (term393 _106193 A k x y).
Proof. exact (MK_COMB (@lem4411209 _106193) (@lem4411208 _106193 A k x y)). Qed.
Lemma lem4411211 {_106193 A : Type'} (y : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term394 _106193 A y k s) = (term394 _106193 A y k s).
Proof. exact (eq_refl (term394 _106193 A y k s)). Qed.
Lemma lem4411212 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term414 _106193 A s k x y) = (term396 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411211 _106193 A y k s) (@lem4411210 _106193 A k x y)). Qed.
Lemma lem4411213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411214 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term420 _106193 A s k x y) = (term421 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411213) (@lem4411212 _106193 A s k x y)). Qed.
Lemma lem4411215 {_106193 A : Type'} (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term417 _106193 A k x y i) = (term386 _106193 A k x y i).
Proof. exact (eq_refl (term417 _106193 A k x y i)). Qed.
Lemma lem4411216 {_106193 A : Type'} (y : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term394 _106193 A y k s) = (term394 _106193 A y k s).
Proof. exact (eq_refl (term394 _106193 A y k s)). Qed.
Lemma lem4411217 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term422 _106193 A s k x y i) = (term423 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4411216 _106193 A y k s) (@lem4411215 _106193 A k x y i)). Qed.
Lemma lem4411218 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term424 _106193 A s k x y) = (term425 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411217 _106193 A s k x y i)). Qed.
Lemma lem4411219 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411220 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term415 _106193 A s k x y) = (term426 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411219 _106193) (@lem4411218 _106193 A s k x y)). Qed.
Lemma lem4411221 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : ((term414 _106193 A s k x y) = (term415 _106193 A s k x y)) = ((term396 _106193 A s k x y) = (term426 _106193 A s k x y)).
Proof. exact (MK_COMB (@lem4411214 _106193 A s k x y) (@lem4411220 _106193 A s k x y)). Qed.
Lemma lem4411222 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term396 _106193 A s k x y) = (term426 _106193 A s k x y).
Proof. exact (EQ_MP (@lem4411221 _106193 A s k x y) (@lem4411206 _106193 A s k x y)). Qed.
Lemma lem4411223 {_106193 A : Type'} (x : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term394 _106193 A x k s) = (term394 _106193 A x k s).
Proof. exact (eq_refl (term394 _106193 A x k s)). Qed.
Lemma lem4411224 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term400 _106193 A s k x y) = (term427 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411223 _106193 A x k s) (@lem4411222 _106193 A s k x y)). Qed.
Lemma lem4411226 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4411227 {_106193 : Type'} (P : Prop) (Q : _106193 -> Prop) : (term241 _106193 P Q) = (term242 _106193 P Q).
Proof. exact (@lem4411226 _106193 P Q). Qed.
Lemma lem4411228 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term428 _106193 A s k x y) = (term429 _106193 A s k x y).
Proof. exact (@lem4411227 _106193 (term416 _106193 A x k s) (term425 _106193 A s k x y)). Qed.
Lemma lem4411229 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term430 _106193 A s k x y i) = (term423 _106193 A s k x y i).
Proof. exact (eq_refl (term430 _106193 A s k x y i)). Qed.
Lemma lem4411230 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term431 _106193 A s k x y) = (term425 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411229 _106193 A s k x y i)). Qed.
Lemma lem4411231 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411232 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term432 _106193 A s k x y) = (term426 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411231 _106193) (@lem4411230 _106193 A s k x y)). Qed.
Lemma lem4411233 {_106193 A : Type'} (x : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term394 _106193 A x k s) = (term394 _106193 A x k s).
Proof. exact (eq_refl (term394 _106193 A x k s)). Qed.
Lemma lem4411234 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term428 _106193 A s k x y) = (term427 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411233 _106193 A x k s) (@lem4411232 _106193 A s k x y)). Qed.
Lemma lem4411235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411236 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term433 _106193 A s k x y) = (term434 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411235) (@lem4411234 _106193 A s k x y)). Qed.
Lemma lem4411237 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term430 _106193 A s k x y i) = (term423 _106193 A s k x y i).
Proof. exact (eq_refl (term430 _106193 A s k x y i)). Qed.
Lemma lem4411238 {_106193 A : Type'} (x : _106193 -> A) (k : _106193 -> Prop) (s : type1413 _106193 A) : (term394 _106193 A x k s) = (term394 _106193 A x k s).
Proof. exact (eq_refl (term394 _106193 A x k s)). Qed.
Lemma lem4411239 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term435 _106193 A s k x y i) = (term436 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4411238 _106193 A x k s) (@lem4411237 _106193 A s k x y i)). Qed.
Lemma lem4411240 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term437 _106193 A s k x y) = (term438 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411239 _106193 A s k x y i)). Qed.
Lemma lem4411241 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411242 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term429 _106193 A s k x y) = (term439 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411241 _106193) (@lem4411240 _106193 A s k x y)). Qed.
Lemma lem4411243 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : ((term428 _106193 A s k x y) = (term429 _106193 A s k x y)) = ((term427 _106193 A s k x y) = (term439 _106193 A s k x y)).
Proof. exact (MK_COMB (@lem4411236 _106193 A s k x y) (@lem4411242 _106193 A s k x y)). Qed.
Lemma lem4411244 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term427 _106193 A s k x y) = (term439 _106193 A s k x y).
Proof. exact (EQ_MP (@lem4411243 _106193 A s k x y) (@lem4411228 _106193 A s k x y)). Qed.
Lemma lem4411245 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term400 _106193 A s k x y) = (term439 _106193 A s k x y).
Proof. exact (TRANS (@lem4411224 _106193 A s k x y) (@lem4411244 _106193 A s k x y)). Qed.
Lemma lem4411246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411247 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term403 _106193 A s k x y) = (term440 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411246) (@lem4411245 _106193 A s k x y)). Qed.
Lemma lem4411248 {_106193 A : Type'} (x : _106193 -> A) (y : _106193 -> A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411249 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term405 _106193 A s k x y) = (term441 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411247 _106193 A s k x y) (@lem4411248 _106193 A x y)). Qed.
Lemma lem4411251 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4411252 {_106193 : Type'} (P : _106193 -> Prop) (Q : Prop) : (term183 _106193 P Q) = (term184 _106193 P Q).
Proof. exact (@lem4411251 _106193 P Q). Qed.
Lemma lem4411253 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term442 _106193 A s k x y) = (term443 _106193 A s k x y).
Proof. exact (@lem4411252 _106193 (term438 _106193 A s k x y) (x = y)). Qed.
Lemma lem4411254 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term444 _106193 A s k x y i) = (term436 _106193 A s k x y i).
Proof. exact (eq_refl (term444 _106193 A s k x y i)). Qed.
Lemma lem4411255 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term445 _106193 A s k x y) = (term438 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411254 _106193 A s k x y i)). Qed.
Lemma lem4411256 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411257 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term446 _106193 A s k x y) = (term439 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411256 _106193) (@lem4411255 _106193 A s k x y)). Qed.
Lemma lem4411258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411259 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term447 _106193 A s k x y) = (term440 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411258) (@lem4411257 _106193 A s k x y)). Qed.
Lemma lem4411260 {_106193 A : Type'} (x : _106193 -> A) (y : _106193 -> A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411261 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term442 _106193 A s k x y) = (term441 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411259 _106193 A s k x y) (@lem4411260 _106193 A x y)). Qed.
Lemma lem4411262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411263 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term448 _106193 A s k x y) = (term449 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411262) (@lem4411261 _106193 A s k x y)). Qed.
Lemma lem4411264 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term444 _106193 A s k x y i) = (term436 _106193 A s k x y i).
Proof. exact (eq_refl (term444 _106193 A s k x y i)). Qed.
Lemma lem4411265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411266 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term450 _106193 A s k x y i) = (term451 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4411265) (@lem4411264 _106193 A s k x y i)). Qed.
Lemma lem4411267 {_106193 A : Type'} (x : _106193 -> A) (y : _106193 -> A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411268 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : _106193) (x : _106193 -> A) (y : _106193 -> A) : (term452 _106193 A s k i x y) = (term453 _106193 A s k i x y).
Proof. exact (MK_COMB (@lem4411266 _106193 A s k x y i) (@lem4411267 _106193 A x y)). Qed.
Lemma lem4411269 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term454 _106193 A s k x y) = (term455 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411268 _106193 A s k i x y)). Qed.
Lemma lem4411270 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411271 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term443 _106193 A s k x y) = (term456 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411270 _106193) (@lem4411269 _106193 A s k x y)). Qed.
Lemma lem4411272 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : ((term442 _106193 A s k x y) = (term443 _106193 A s k x y)) = ((term441 _106193 A s k x y) = (term456 _106193 A s k x y)).
Proof. exact (MK_COMB (@lem4411263 _106193 A s k x y) (@lem4411271 _106193 A s k x y)). Qed.
Lemma lem4411273 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term441 _106193 A s k x y) = (term456 _106193 A s k x y).
Proof. exact (EQ_MP (@lem4411272 _106193 A s k x y) (@lem4411253 _106193 A s k x y)). Qed.
Lemma lem4411274 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term405 _106193 A s k x y) = (term456 _106193 A s k x y).
Proof. exact (TRANS (@lem4411249 _106193 A s k x y) (@lem4411273 _106193 A s k x y)). Qed.
Lemma lem4411275 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term406 _106193 A s k x) = (term457 _106193 A s k x).
Proof. exact (fun_ext (fun y : _106193 -> A => @lem4411274 _106193 A s k x y)). Qed.
Lemma lem4411276 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411277 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term407 _106193 A s k x) = (term458 _106193 A s k x).
Proof. exact (MK_COMB (@lem4411276 _106193 A) (@lem4411275 _106193 A s k x)). Qed.
Lemma lem4411279 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411280 {_106193 A : Type'} (P : type551 _106193 A) : (term459 _106193 A P) = (term460 _106193 A P).
Proof. exact (@lem4411279 (_106193 -> A) _106193 P). Qed.
Lemma lem4411281 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term461 _106193 A s k x) = (term462 _106193 A s k x).
Proof. exact (@lem4411280 _106193 A (term463 _106193 A s k x)). Qed.
Lemma lem4411282 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term464 _106193 A s k x y) = (term455 _106193 A s k x y).
Proof. exact (eq_refl (term464 _106193 A s k x y)). Qed.
Lemma lem4411283 {_106193 : Type'} (i : _106193) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411284 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) (i : _106193) : (term465 _106193 A s k x y i) = (term466 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4411282 _106193 A s k x y) (@lem4411283 _106193 i)). Qed.
Lemma lem4411285 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : _106193) (x : _106193 -> A) (y : _106193 -> A) : (term466 _106193 A s k x y i) = (term453 _106193 A s k i x y).
Proof. exact (eq_refl (term466 _106193 A s k x y i)). Qed.
Lemma lem4411286 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : _106193) (x : _106193 -> A) (y : _106193 -> A) : (term465 _106193 A s k x y i) = (term453 _106193 A s k i x y).
Proof. exact (TRANS (@lem4411284 _106193 A s k x y i) (@lem4411285 _106193 A s k i x y)). Qed.
Lemma lem4411287 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term467 _106193 A s k x y) = (term455 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4411286 _106193 A s k i x y)). Qed.
Lemma lem4411288 {_106193 : Type'} : (@ex _106193) = (@ex _106193).
Proof. exact (eq_refl (@ex _106193)). Qed.
Lemma lem4411289 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term468 _106193 A s k x y) = (term456 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4411288 _106193) (@lem4411287 _106193 A s k x y)). Qed.
Lemma lem4411290 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term469 _106193 A s k x) = (term457 _106193 A s k x).
Proof. exact (fun_ext (fun y : _106193 -> A => @lem4411289 _106193 A s k x y)). Qed.
Lemma lem4411291 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411292 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term461 _106193 A s k x) = (term458 _106193 A s k x).
Proof. exact (MK_COMB (@lem4411291 _106193 A) (@lem4411290 _106193 A s k x)). Qed.
Lemma lem4411293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411294 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term470 _106193 A s k x) = (term471 _106193 A s k x).
Proof. exact (MK_COMB (@lem4411293) (@lem4411292 _106193 A s k x)). Qed.
Lemma lem4411295 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (y : _106193 -> A) : (term464 _106193 A s k x y) = (term455 _106193 A s k x y).
Proof. exact (eq_refl (term464 _106193 A s k x y)). Qed.
Lemma lem4411296 {_106193 A : Type'} (i : type569 _106193 A) (y : _106193 -> A) : (i y) = (i y).
Proof. exact (eq_refl (i y)). Qed.
Lemma lem4411297 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (i : type569 _106193 A) (y : _106193 -> A) : (term472 _106193 A s k x i y) = (term473 _106193 A s k x i y).
Proof. exact (MK_COMB (@lem4411295 _106193 A s k x y) (@lem4411296 _106193 A i y)). Qed.
Lemma lem4411298 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type569 _106193 A) (x : _106193 -> A) (y : _106193 -> A) : (term473 _106193 A s k x i y) = (term474 _106193 A s k i x y).
Proof. exact (eq_refl (term473 _106193 A s k x i y)). Qed.
Lemma lem4411299 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type569 _106193 A) (x : _106193 -> A) (y : _106193 -> A) : (term472 _106193 A s k x i y) = (term474 _106193 A s k i x y).
Proof. exact (TRANS (@lem4411297 _106193 A s k x i y) (@lem4411298 _106193 A s k i x y)). Qed.
Lemma lem4411300 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type569 _106193 A) (x : _106193 -> A) : (term475 _106193 A s k x i) = (term476 _106193 A s k i x).
Proof. exact (fun_ext (fun y : _106193 -> A => @lem4411299 _106193 A s k i x y)). Qed.
Lemma lem4411301 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411302 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type569 _106193 A) (x : _106193 -> A) : (term477 _106193 A s k x i) = (term478 _106193 A s k i x).
Proof. exact (MK_COMB (@lem4411301 _106193 A) (@lem4411300 _106193 A s k i x)). Qed.
Lemma lem4411303 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term479 _106193 A s k x) = (term480 _106193 A s k x).
Proof. exact (fun_ext (fun i : type569 _106193 A => @lem4411302 _106193 A s k i x)). Qed.
Lemma lem4411304 {_106193 A : Type'} : (@ex ((_106193 -> A) -> _106193)) = (@ex ((_106193 -> A) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> A) -> _106193))). Qed.
Lemma lem4411305 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term462 _106193 A s k x) = (term481 _106193 A s k x).
Proof. exact (MK_COMB (@lem4411304 _106193 A) (@lem4411303 _106193 A s k x)). Qed.
Lemma lem4411306 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : ((term461 _106193 A s k x) = (term462 _106193 A s k x)) = ((term458 _106193 A s k x) = (term481 _106193 A s k x)).
Proof. exact (MK_COMB (@lem4411294 _106193 A s k x) (@lem4411305 _106193 A s k x)). Qed.
Lemma lem4411307 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term458 _106193 A s k x) = (term481 _106193 A s k x).
Proof. exact (EQ_MP (@lem4411306 _106193 A s k x) (@lem4411281 _106193 A s k x)). Qed.
Lemma lem4411308 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term407 _106193 A s k x) = (term481 _106193 A s k x).
Proof. exact (TRANS (@lem4411277 _106193 A s k x) (@lem4411307 _106193 A s k x)). Qed.
Lemma lem4411309 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term408 _106193 A s k) = (term482 _106193 A s k).
Proof. exact (fun_ext (fun x : _106193 -> A => @lem4411308 _106193 A s k x)). Qed.
Lemma lem4411310 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411311 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term409 _106193 A s k) = (term483 _106193 A s k).
Proof. exact (MK_COMB (@lem4411310 _106193 A) (@lem4411309 _106193 A s k)). Qed.
Lemma lem4411313 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411314 {_106193 A : Type'} (P : type499 _106193 A) : (term484 _106193 A P) = (term485 _106193 A P).
Proof. exact (@lem4411313 (_106193 -> A) (type569 _106193 A) P). Qed.
Lemma lem4411315 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term486 _106193 A s k) = (term487 _106193 A s k).
Proof. exact (@lem4411314 _106193 A (term488 _106193 A s k)). Qed.
Lemma lem4411316 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term489 _106193 A s k x) = (term480 _106193 A s k x).
Proof. exact (eq_refl (term489 _106193 A s k x)). Qed.
Lemma lem4411317 {_106193 A : Type'} (i : type569 _106193 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411318 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) (i : type569 _106193 A) : (term490 _106193 A s k x i) = (term491 _106193 A s k x i).
Proof. exact (MK_COMB (@lem4411316 _106193 A s k x) (@lem4411317 _106193 A i)). Qed.
Lemma lem4411319 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type569 _106193 A) (x : _106193 -> A) : (term491 _106193 A s k x i) = (term478 _106193 A s k i x).
Proof. exact (eq_refl (term491 _106193 A s k x i)). Qed.
Lemma lem4411320 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type569 _106193 A) (x : _106193 -> A) : (term490 _106193 A s k x i) = (term478 _106193 A s k i x).
Proof. exact (TRANS (@lem4411318 _106193 A s k x i) (@lem4411319 _106193 A s k i x)). Qed.
Lemma lem4411321 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term492 _106193 A s k x) = (term480 _106193 A s k x).
Proof. exact (fun_ext (fun i : type569 _106193 A => @lem4411320 _106193 A s k i x)). Qed.
Lemma lem4411322 {_106193 A : Type'} : (@ex ((_106193 -> A) -> _106193)) = (@ex ((_106193 -> A) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> A) -> _106193))). Qed.
Lemma lem4411323 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term493 _106193 A s k x) = (term481 _106193 A s k x).
Proof. exact (MK_COMB (@lem4411322 _106193 A) (@lem4411321 _106193 A s k x)). Qed.
Lemma lem4411324 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term494 _106193 A s k) = (term482 _106193 A s k).
Proof. exact (fun_ext (fun x : _106193 -> A => @lem4411323 _106193 A s k x)). Qed.
Lemma lem4411325 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411326 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term486 _106193 A s k) = (term483 _106193 A s k).
Proof. exact (MK_COMB (@lem4411325 _106193 A) (@lem4411324 _106193 A s k)). Qed.
Lemma lem4411327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411328 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term495 _106193 A s k) = (term496 _106193 A s k).
Proof. exact (MK_COMB (@lem4411327) (@lem4411326 _106193 A s k)). Qed.
Lemma lem4411329 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (x : _106193 -> A) : (term489 _106193 A s k x) = (term480 _106193 A s k x).
Proof. exact (eq_refl (term489 _106193 A s k x)). Qed.
Lemma lem4411330 {_106193 A : Type'} (i : type522 _106193 A) (x : _106193 -> A) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem4411331 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) (x : _106193 -> A) : (term497 _106193 A s k i x) = (term498 _106193 A s k i x).
Proof. exact (MK_COMB (@lem4411329 _106193 A s k x) (@lem4411330 _106193 A i x)). Qed.
Lemma lem4411332 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) (x : _106193 -> A) : (term498 _106193 A s k i x) = (term499 _106193 A s k i x).
Proof. exact (eq_refl (term498 _106193 A s k i x)). Qed.
Lemma lem4411333 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) (x : _106193 -> A) : (term497 _106193 A s k i x) = (term499 _106193 A s k i x).
Proof. exact (TRANS (@lem4411331 _106193 A s k i x) (@lem4411332 _106193 A s k i x)). Qed.
Lemma lem4411334 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) : (term500 _106193 A s k i) = (term501 _106193 A s k i).
Proof. exact (fun_ext (fun x : _106193 -> A => @lem4411333 _106193 A s k i x)). Qed.
Lemma lem4411335 {_106193 A : Type'} : (@all (_106193 -> A)) = (@all (_106193 -> A)).
Proof. exact (eq_refl (@all (_106193 -> A))). Qed.
Lemma lem4411336 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) : (term502 _106193 A s k i) = (term503 _106193 A s k i).
Proof. exact (MK_COMB (@lem4411335 _106193 A) (@lem4411334 _106193 A s k i)). Qed.
Lemma lem4411337 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term504 _106193 A s k) = (term505 _106193 A s k).
Proof. exact (fun_ext (fun i : type522 _106193 A => @lem4411336 _106193 A s k i)). Qed.
Lemma lem4411338 {_106193 A : Type'} : (@ex ((_106193 -> A) -> (_106193 -> A) -> _106193)) = (@ex ((_106193 -> A) -> (_106193 -> A) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> A) -> (_106193 -> A) -> _106193))). Qed.
Lemma lem4411339 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term487 _106193 A s k) = (term506 _106193 A s k).
Proof. exact (MK_COMB (@lem4411338 _106193 A) (@lem4411337 _106193 A s k)). Qed.
Lemma lem4411340 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : ((term486 _106193 A s k) = (term487 _106193 A s k)) = ((term483 _106193 A s k) = (term506 _106193 A s k)).
Proof. exact (MK_COMB (@lem4411328 _106193 A s k) (@lem4411339 _106193 A s k)). Qed.
Lemma lem4411341 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term483 _106193 A s k) = (term506 _106193 A s k).
Proof. exact (EQ_MP (@lem4411340 _106193 A s k) (@lem4411315 _106193 A s k)). Qed.
Lemma lem4411342 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term409 _106193 A s k) = (term506 _106193 A s k).
Proof. exact (TRANS (@lem4411311 _106193 A s k) (@lem4411341 _106193 A s k)). Qed.
Lemma lem4411343 {_106193 A : Type'} (k : _106193 -> Prop) : (term410 _106193 A k) = (term507 _106193 A k).
Proof. exact (fun_ext (fun s : type1413 _106193 A => @lem4411342 _106193 A s k)). Qed.
Lemma lem4411344 {_106193 A : Type'} : (@all (_106193 -> A -> Prop)) = (@all (_106193 -> A -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> A -> Prop))). Qed.
Lemma lem4411345 {_106193 A : Type'} (k : _106193 -> Prop) : (term411 _106193 A k) = (term508 _106193 A k).
Proof. exact (MK_COMB (@lem4411344 _106193 A) (@lem4411343 _106193 A k)). Qed.
Lemma lem4411347 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411348 {_106193 A : Type'} (P : type445 _106193 A) : (term509 _106193 A P) = (term510 _106193 A P).
Proof. exact (@lem4411347 (type1413 _106193 A) (type522 _106193 A) P). Qed.
Lemma lem4411349 {_106193 A : Type'} (k : _106193 -> Prop) : (term511 _106193 A k) = (term512 _106193 A k).
Proof. exact (@lem4411348 _106193 A (term513 _106193 A k)). Qed.
Lemma lem4411350 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term514 _106193 A k s) = (term505 _106193 A s k).
Proof. exact (eq_refl (term514 _106193 A k s)). Qed.
Lemma lem4411351 {_106193 A : Type'} (i : type522 _106193 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411352 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) : (term515 _106193 A k s i) = (term516 _106193 A s k i).
Proof. exact (MK_COMB (@lem4411350 _106193 A s k) (@lem4411351 _106193 A i)). Qed.
Lemma lem4411353 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) : (term516 _106193 A s k i) = (term503 _106193 A s k i).
Proof. exact (eq_refl (term516 _106193 A s k i)). Qed.
Lemma lem4411354 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) (i : type522 _106193 A) : (term515 _106193 A k s i) = (term503 _106193 A s k i).
Proof. exact (TRANS (@lem4411352 _106193 A s k i) (@lem4411353 _106193 A s k i)). Qed.
Lemma lem4411355 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term517 _106193 A k s) = (term505 _106193 A s k).
Proof. exact (fun_ext (fun i : type522 _106193 A => @lem4411354 _106193 A s k i)). Qed.
Lemma lem4411356 {_106193 A : Type'} : (@ex ((_106193 -> A) -> (_106193 -> A) -> _106193)) = (@ex ((_106193 -> A) -> (_106193 -> A) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> A) -> (_106193 -> A) -> _106193))). Qed.
Lemma lem4411357 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term518 _106193 A k s) = (term506 _106193 A s k).
Proof. exact (MK_COMB (@lem4411356 _106193 A) (@lem4411355 _106193 A s k)). Qed.
Lemma lem4411358 {_106193 A : Type'} (k : _106193 -> Prop) : (term519 _106193 A k) = (term507 _106193 A k).
Proof. exact (fun_ext (fun s : type1413 _106193 A => @lem4411357 _106193 A s k)). Qed.
Lemma lem4411359 {_106193 A : Type'} : (@all (_106193 -> A -> Prop)) = (@all (_106193 -> A -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> A -> Prop))). Qed.
Lemma lem4411360 {_106193 A : Type'} (k : _106193 -> Prop) : (term511 _106193 A k) = (term508 _106193 A k).
Proof. exact (MK_COMB (@lem4411359 _106193 A) (@lem4411358 _106193 A k)). Qed.
Lemma lem4411361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411362 {_106193 A : Type'} (k : _106193 -> Prop) : (term520 _106193 A k) = (term521 _106193 A k).
Proof. exact (MK_COMB (@lem4411361) (@lem4411360 _106193 A k)). Qed.
Lemma lem4411363 {_106193 A : Type'} (s : type1413 _106193 A) (k : _106193 -> Prop) : (term514 _106193 A k s) = (term505 _106193 A s k).
Proof. exact (eq_refl (term514 _106193 A k s)). Qed.
Lemma lem4411364 {_106193 A : Type'} (i : type453 _106193 A) (s : type1413 _106193 A) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem4411365 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) (s : type1413 _106193 A) : (term522 _106193 A k i s) = (term523 _106193 A k i s).
Proof. exact (MK_COMB (@lem4411363 _106193 A s k) (@lem4411364 _106193 A i s)). Qed.
Lemma lem4411366 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) (s : type1413 _106193 A) : (term523 _106193 A k i s) = (term524 _106193 A k i s).
Proof. exact (eq_refl (term523 _106193 A k i s)). Qed.
Lemma lem4411367 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) (s : type1413 _106193 A) : (term522 _106193 A k i s) = (term524 _106193 A k i s).
Proof. exact (TRANS (@lem4411365 _106193 A k i s) (@lem4411366 _106193 A k i s)). Qed.
Lemma lem4411368 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) : (term525 _106193 A k i) = (term526 _106193 A k i).
Proof. exact (fun_ext (fun s : type1413 _106193 A => @lem4411367 _106193 A k i s)). Qed.
Lemma lem4411369 {_106193 A : Type'} : (@all (_106193 -> A -> Prop)) = (@all (_106193 -> A -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> A -> Prop))). Qed.
Lemma lem4411370 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) : (term527 _106193 A k i) = (term528 _106193 A k i).
Proof. exact (MK_COMB (@lem4411369 _106193 A) (@lem4411368 _106193 A k i)). Qed.
Lemma lem4411371 {_106193 A : Type'} (k : _106193 -> Prop) : (term529 _106193 A k) = (term530 _106193 A k).
Proof. exact (fun_ext (fun i : type453 _106193 A => @lem4411370 _106193 A k i)). Qed.
Lemma lem4411372 {_106193 A : Type'} : (@ex ((_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193)) = (@ex ((_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193))). Qed.
Lemma lem4411373 {_106193 A : Type'} (k : _106193 -> Prop) : (term512 _106193 A k) = (term531 _106193 A k).
Proof. exact (MK_COMB (@lem4411372 _106193 A) (@lem4411371 _106193 A k)). Qed.
Lemma lem4411374 {_106193 A : Type'} (k : _106193 -> Prop) : ((term511 _106193 A k) = (term512 _106193 A k)) = ((term508 _106193 A k) = (term531 _106193 A k)).
Proof. exact (MK_COMB (@lem4411362 _106193 A k) (@lem4411373 _106193 A k)). Qed.
Lemma lem4411375 {_106193 A : Type'} (k : _106193 -> Prop) : (term508 _106193 A k) = (term531 _106193 A k).
Proof. exact (EQ_MP (@lem4411374 _106193 A k) (@lem4411349 _106193 A k)). Qed.
Lemma lem4411376 {_106193 A : Type'} (k : _106193 -> Prop) : (term411 _106193 A k) = (term531 _106193 A k).
Proof. exact (TRANS (@lem4411345 _106193 A k) (@lem4411375 _106193 A k)). Qed.
Lemma lem4411377 {_106193 A : Type'} : (term412 _106193 A) = (term532 _106193 A).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4411376 _106193 A k)). Qed.
Lemma lem4411378 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4411379 {_106193 A : Type'} : (term413 _106193 A) = (term533 _106193 A).
Proof. exact (MK_COMB (@lem4411378 _106193) (@lem4411377 _106193 A)). Qed.
Lemma lem4411381 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411382 {_106193 A : Type'} (P : type581 _106193 A) : (term534 _106193 A P) = (term535 _106193 A P).
Proof. exact (@lem4411381 (_106193 -> Prop) (type453 _106193 A) P). Qed.
Lemma lem4411383 {_106193 A : Type'} : (term536 _106193 A) = (term537 _106193 A).
Proof. exact (@lem4411382 _106193 A (term538 _106193 A)). Qed.
Lemma lem4411384 {_106193 A : Type'} (k : _106193 -> Prop) : (term539 _106193 A k) = (term530 _106193 A k).
Proof. exact (eq_refl (term539 _106193 A k)). Qed.
Lemma lem4411385 {_106193 A : Type'} (i : type453 _106193 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411386 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) : (term540 _106193 A k i) = (term541 _106193 A k i).
Proof. exact (MK_COMB (@lem4411384 _106193 A k) (@lem4411385 _106193 A i)). Qed.
Lemma lem4411387 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) : (term541 _106193 A k i) = (term528 _106193 A k i).
Proof. exact (eq_refl (term541 _106193 A k i)). Qed.
Lemma lem4411388 {_106193 A : Type'} (k : _106193 -> Prop) (i : type453 _106193 A) : (term540 _106193 A k i) = (term528 _106193 A k i).
Proof. exact (TRANS (@lem4411386 _106193 A k i) (@lem4411387 _106193 A k i)). Qed.
Lemma lem4411389 {_106193 A : Type'} (k : _106193 -> Prop) : (term542 _106193 A k) = (term530 _106193 A k).
Proof. exact (fun_ext (fun i : type453 _106193 A => @lem4411388 _106193 A k i)). Qed.
Lemma lem4411390 {_106193 A : Type'} : (@ex ((_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193)) = (@ex ((_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193))). Qed.
Lemma lem4411391 {_106193 A : Type'} (k : _106193 -> Prop) : (term543 _106193 A k) = (term531 _106193 A k).
Proof. exact (MK_COMB (@lem4411390 _106193 A) (@lem4411389 _106193 A k)). Qed.
Lemma lem4411392 {_106193 A : Type'} : (term544 _106193 A) = (term532 _106193 A).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4411391 _106193 A k)). Qed.
Lemma lem4411393 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4411394 {_106193 A : Type'} : (term536 _106193 A) = (term533 _106193 A).
Proof. exact (MK_COMB (@lem4411393 _106193) (@lem4411392 _106193 A)). Qed.
Lemma lem4411395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411396 {_106193 A : Type'} : (term545 _106193 A) = (term546 _106193 A).
Proof. exact (MK_COMB (@lem4411395) (@lem4411394 _106193 A)). Qed.
Lemma lem4411397 {_106193 A : Type'} (k : _106193 -> Prop) : (term539 _106193 A k) = (term530 _106193 A k).
Proof. exact (eq_refl (term539 _106193 A k)). Qed.
Lemma lem4411398 {_106193 A : Type'} (i : type614 _106193 A) (k : _106193 -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem4411399 {_106193 A : Type'} (i : type614 _106193 A) (k : _106193 -> Prop) : (term547 _106193 A i k) = (term548 _106193 A i k).
Proof. exact (MK_COMB (@lem4411397 _106193 A k) (@lem4411398 _106193 A i k)). Qed.
Lemma lem4411400 {_106193 A : Type'} (i : type614 _106193 A) (k : _106193 -> Prop) : (term548 _106193 A i k) = (term549 _106193 A i k).
Proof. exact (eq_refl (term548 _106193 A i k)). Qed.
Lemma lem4411401 {_106193 A : Type'} (i : type614 _106193 A) (k : _106193 -> Prop) : (term547 _106193 A i k) = (term549 _106193 A i k).
Proof. exact (TRANS (@lem4411399 _106193 A i k) (@lem4411400 _106193 A i k)). Qed.
Lemma lem4411402 {_106193 A : Type'} (i : type614 _106193 A) : (term550 _106193 A i) = (term551 _106193 A i).
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4411401 _106193 A i k)). Qed.
Lemma lem4411403 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4411404 {_106193 A : Type'} (i : type614 _106193 A) : (term552 _106193 A i) = (term553 _106193 A i).
Proof. exact (MK_COMB (@lem4411403 _106193) (@lem4411402 _106193 A i)). Qed.
Lemma lem4411405 {_106193 A : Type'} : (term554 _106193 A) = (term555 _106193 A).
Proof. exact (fun_ext (fun i : type614 _106193 A => @lem4411404 _106193 A i)). Qed.
Lemma lem4411406 {_106193 A : Type'} : (@ex ((_106193 -> Prop) -> (_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193)) = (@ex ((_106193 -> Prop) -> (_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193)).
Proof. exact (eq_refl (@ex ((_106193 -> Prop) -> (_106193 -> A -> Prop) -> (_106193 -> A) -> (_106193 -> A) -> _106193))). Qed.
Lemma lem4411407 {_106193 A : Type'} : (term537 _106193 A) = (term556 _106193 A).
Proof. exact (MK_COMB (@lem4411406 _106193 A) (@lem4411405 _106193 A)). Qed.
Lemma lem4411408 {_106193 A : Type'} : ((term536 _106193 A) = (term537 _106193 A)) = ((term533 _106193 A) = (term556 _106193 A)).
Proof. exact (MK_COMB (@lem4411396 _106193 A) (@lem4411407 _106193 A)). Qed.
Lemma lem4411409 {_106193 A : Type'} : (term533 _106193 A) = (term556 _106193 A).
Proof. exact (EQ_MP (@lem4411408 _106193 A) (@lem4411383 _106193 A)). Qed.
Lemma lem4411411 {_106193 A : Type'} : (term413 _106193 A) = (term556 _106193 A).
Proof. exact (TRANS (@lem4411379 _106193 A) (@lem4411409 _106193 A)). Qed.
Lemma lem4411412 {_106193 A : Type'} : (term13 _106193 A) = (term556 _106193 A).
Proof. exact (TRANS (@lem4411093 _106193 A) (@lem4411411 _106193 A)). Qed.
Lemma lem4411413 {_106193 A : Type'} (h1 : term13 _106193 A) : term556 _106193 A.
Proof. exact (EQ_MP (@lem4411412 _106193 A) (@lem4410342 _106193 A h1)). Qed.
Lemma lem4411422 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term104 _106189 K k x y i) = (term105 _106189 K k x y i).
Proof. exact (@lem17362 (@IN K i k) ((x i) = (y i))). Qed.
Lemma lem4411423 {K : Type'} (P : K -> Prop) : (term107 K P) = (term108 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4411424 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term109 _106189 K k x y) = (term110 _106189 K k x y).
Proof. exact (@lem4411423 K (term65 _106189 K k x y)). Qed.
Lemma lem4411425 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term111 _106189 K k x y i) = (term64 _106189 K k x y i).
Proof. exact (eq_refl (term111 _106189 K k x y i)). Qed.
Lemma lem4411426 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4411427 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term112 _106189 K k x y i) = (term104 _106189 K k x y i).
Proof. exact (MK_COMB (@lem4411426) (@lem4411425 _106189 K k x y i)). Qed.
Lemma lem4411428 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term112 _106189 K k x y i) = (term105 _106189 K k x y i).
Proof. exact (TRANS (@lem4411427 _106189 K k x y i) (@lem4411422 _106189 K k x y i)). Qed.
Lemma lem4411429 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term113 _106189 K k x y) = (term114 _106189 K k x y).
Proof. exact (fun_ext (fun i : K => @lem4411428 _106189 K k x y i)). Qed.
Lemma lem4411430 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411431 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term110 _106189 K k x y) = (term115 _106189 K k x y).
Proof. exact (MK_COMB (@lem4411430 K) (@lem4411429 _106189 K k x y)). Qed.
Lemma lem4411432 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term109 _106189 K k x y) = (term115 _106189 K k x y).
Proof. exact (TRANS (@lem4411424 _106189 K k x y) (@lem4411431 _106189 K k x y)). Qed.
Lemma lem4411434 {_106189 K : Type'} (y : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term221 _106189 K y k s) = (term221 _106189 K y k s).
Proof. exact (eq_refl (term221 _106189 K y k s)). Qed.
Lemma lem4411435 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term222 _106189 K s k x y) = (term223 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411434 _106189 K y k s) (@lem4411432 _106189 K k x y)). Qed.
Lemma lem4411436 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term224 _106189 K s k x y) = (term222 _106189 K s k x y).
Proof. exact (@lem17045 (term225 _106189 K y k s) (term66 _106189 K k x y)). Qed.
Lemma lem4411437 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term224 _106189 K s k x y) = (term223 _106189 K s k x y).
Proof. exact (TRANS (@lem4411436 _106189 K s k x y) (@lem4411435 _106189 K s k x y)). Qed.
Lemma lem4411439 {_106189 K : Type'} (x : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term221 _106189 K x k s) = (term221 _106189 K x k s).
Proof. exact (eq_refl (term221 _106189 K x k s)). Qed.
Lemma lem4411440 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term226 _106189 K s k x y) = (term227 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411439 _106189 K x k s) (@lem4411437 _106189 K s k x y)). Qed.
Lemma lem4411441 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term228 _106189 K s k x y) = (term226 _106189 K s k x y).
Proof. exact (@lem17045 (term225 _106189 K x k s) (term68 _106189 K s k x y)). Qed.
Lemma lem4411442 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term228 _106189 K s k x y) = (term227 _106189 K s k x y).
Proof. exact (TRANS (@lem4411441 _106189 K s k x y) (@lem4411440 _106189 K s k x y)). Qed.
Lemma lem4411443 {_106189 K : Type'} (x : K -> _106189) (y : K -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411445 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term229 _106189 K s k x y) = (term230 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411444) (@lem4411442 _106189 K s k x y)). Qed.
Lemma lem4411446 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term231 _106189 K s k x y) = (term232 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411445 _106189 K s k x y) (@lem4411443 _106189 K x y)). Qed.
Lemma lem4411447 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term71 _106189 K s k x y) = (term231 _106189 K s k x y).
Proof. exact (@lem17265 (term69 _106189 K s k x y) (x = y)). Qed.
Lemma lem4411448 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term71 _106189 K s k x y) = (term232 _106189 K s k x y).
Proof. exact (TRANS (@lem4411447 _106189 K s k x y) (@lem4411446 _106189 K s k x y)). Qed.
Lemma lem4411449 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term72 _106189 K s k x) = (term233 _106189 K s k x).
Proof. exact (fun_ext (fun y : K -> _106189 => @lem4411448 _106189 K s k x y)). Qed.
Lemma lem4411450 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411451 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term73 _106189 K s k x) = (term234 _106189 K s k x).
Proof. exact (MK_COMB (@lem4411450 _106189 K) (@lem4411449 _106189 K s k x)). Qed.
Lemma lem4411452 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term74 _106189 K s k) = (term235 _106189 K s k).
Proof. exact (fun_ext (fun x : K -> _106189 => @lem4411451 _106189 K s k x)). Qed.
Lemma lem4411453 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411454 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term75 _106189 K s k) = (term236 _106189 K s k).
Proof. exact (MK_COMB (@lem4411453 _106189 K) (@lem4411452 _106189 K s k)). Qed.
Lemma lem4411455 {_106189 K : Type'} (k : K -> Prop) : (term76 _106189 K k) = (term237 _106189 K k).
Proof. exact (fun_ext (fun s : type1470 _106189 K => @lem4411454 _106189 K s k)). Qed.
Lemma lem4411456 {_106189 K : Type'} : (@all (K -> _106189 -> Prop)) = (@all (K -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (K -> _106189 -> Prop))). Qed.
Lemma lem4411457 {_106189 K : Type'} (k : K -> Prop) : (term77 _106189 K k) = (term238 _106189 K k).
Proof. exact (MK_COMB (@lem4411456 _106189 K) (@lem4411455 _106189 K k)). Qed.
Lemma lem4411458 {_106189 K : Type'} : (term78 _106189 K) = (term239 _106189 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4411457 _106189 K k)). Qed.
Lemma lem4411459 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4411460 {_106189 K : Type'} : (term11 _106189 K) = (term240 _106189 K).
Proof. exact (MK_COMB (@lem4411459 K) (@lem4411458 _106189 K)). Qed.
Lemma lem4411571 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4411572 {K : Type'} (P : Prop) (Q : K -> Prop) : (term241 K P Q) = (term242 K P Q).
Proof. exact (@lem4411571 K P Q). Qed.
Lemma lem4411573 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term243 _106189 K s k x y) = (term244 _106189 K s k x y).
Proof. exact (@lem4411572 K (term245 _106189 K y k s) (term114 _106189 K k x y)). Qed.
Lemma lem4411574 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term171 _106189 K k x y i) = (term105 _106189 K k x y i).
Proof. exact (eq_refl (term171 _106189 K k x y i)). Qed.
Lemma lem4411575 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term172 _106189 K k x y) = (term114 _106189 K k x y).
Proof. exact (fun_ext (fun i : K => @lem4411574 _106189 K k x y i)). Qed.
Lemma lem4411576 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411577 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term173 _106189 K k x y) = (term115 _106189 K k x y).
Proof. exact (MK_COMB (@lem4411576 K) (@lem4411575 _106189 K k x y)). Qed.
Lemma lem4411578 {_106189 K : Type'} (y : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term221 _106189 K y k s) = (term221 _106189 K y k s).
Proof. exact (eq_refl (term221 _106189 K y k s)). Qed.
Lemma lem4411579 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term243 _106189 K s k x y) = (term223 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411578 _106189 K y k s) (@lem4411577 _106189 K k x y)). Qed.
Lemma lem4411580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411581 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term246 _106189 K s k x y) = (term247 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411580) (@lem4411579 _106189 K s k x y)). Qed.
Lemma lem4411582 {_106189 K : Type'} (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term171 _106189 K k x y i) = (term105 _106189 K k x y i).
Proof. exact (eq_refl (term171 _106189 K k x y i)). Qed.
Lemma lem4411583 {_106189 K : Type'} (y : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term221 _106189 K y k s) = (term221 _106189 K y k s).
Proof. exact (eq_refl (term221 _106189 K y k s)). Qed.
Lemma lem4411584 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term248 _106189 K s k x y i) = (term249 _106189 K s k x y i).
Proof. exact (MK_COMB (@lem4411583 _106189 K y k s) (@lem4411582 _106189 K k x y i)). Qed.
Lemma lem4411585 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term250 _106189 K s k x y) = (term251 _106189 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411584 _106189 K s k x y i)). Qed.
Lemma lem4411586 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411587 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term244 _106189 K s k x y) = (term252 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411586 K) (@lem4411585 _106189 K s k x y)). Qed.
Lemma lem4411588 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : ((term243 _106189 K s k x y) = (term244 _106189 K s k x y)) = ((term223 _106189 K s k x y) = (term252 _106189 K s k x y)).
Proof. exact (MK_COMB (@lem4411581 _106189 K s k x y) (@lem4411587 _106189 K s k x y)). Qed.
Lemma lem4411589 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term223 _106189 K s k x y) = (term252 _106189 K s k x y).
Proof. exact (EQ_MP (@lem4411588 _106189 K s k x y) (@lem4411573 _106189 K s k x y)). Qed.
Lemma lem4411590 {_106189 K : Type'} (x : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term221 _106189 K x k s) = (term221 _106189 K x k s).
Proof. exact (eq_refl (term221 _106189 K x k s)). Qed.
Lemma lem4411591 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term227 _106189 K s k x y) = (term253 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411590 _106189 K x k s) (@lem4411589 _106189 K s k x y)). Qed.
Lemma lem4411593 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4411594 {K : Type'} (P : Prop) (Q : K -> Prop) : (term241 K P Q) = (term242 K P Q).
Proof. exact (@lem4411593 K P Q). Qed.
Lemma lem4411595 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term254 _106189 K s k x y) = (term255 _106189 K s k x y).
Proof. exact (@lem4411594 K (term245 _106189 K x k s) (term251 _106189 K s k x y)). Qed.
Lemma lem4411596 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term256 _106189 K s k x y i) = (term249 _106189 K s k x y i).
Proof. exact (eq_refl (term256 _106189 K s k x y i)). Qed.
Lemma lem4411597 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term257 _106189 K s k x y) = (term251 _106189 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411596 _106189 K s k x y i)). Qed.
Lemma lem4411598 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411599 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term258 _106189 K s k x y) = (term252 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411598 K) (@lem4411597 _106189 K s k x y)). Qed.
Lemma lem4411600 {_106189 K : Type'} (x : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term221 _106189 K x k s) = (term221 _106189 K x k s).
Proof. exact (eq_refl (term221 _106189 K x k s)). Qed.
Lemma lem4411601 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term254 _106189 K s k x y) = (term253 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411600 _106189 K x k s) (@lem4411599 _106189 K s k x y)). Qed.
Lemma lem4411602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411603 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term259 _106189 K s k x y) = (term260 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411602) (@lem4411601 _106189 K s k x y)). Qed.
Lemma lem4411604 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term256 _106189 K s k x y i) = (term249 _106189 K s k x y i).
Proof. exact (eq_refl (term256 _106189 K s k x y i)). Qed.
Lemma lem4411605 {_106189 K : Type'} (x : K -> _106189) (k : K -> Prop) (s : type1470 _106189 K) : (term221 _106189 K x k s) = (term221 _106189 K x k s).
Proof. exact (eq_refl (term221 _106189 K x k s)). Qed.
Lemma lem4411606 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term261 _106189 K s k x y i) = (term262 _106189 K s k x y i).
Proof. exact (MK_COMB (@lem4411605 _106189 K x k s) (@lem4411604 _106189 K s k x y i)). Qed.
Lemma lem4411607 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term263 _106189 K s k x y) = (term264 _106189 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411606 _106189 K s k x y i)). Qed.
Lemma lem4411608 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411609 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term255 _106189 K s k x y) = (term265 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411608 K) (@lem4411607 _106189 K s k x y)). Qed.
Lemma lem4411610 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : ((term254 _106189 K s k x y) = (term255 _106189 K s k x y)) = ((term253 _106189 K s k x y) = (term265 _106189 K s k x y)).
Proof. exact (MK_COMB (@lem4411603 _106189 K s k x y) (@lem4411609 _106189 K s k x y)). Qed.
Lemma lem4411611 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term253 _106189 K s k x y) = (term265 _106189 K s k x y).
Proof. exact (EQ_MP (@lem4411610 _106189 K s k x y) (@lem4411595 _106189 K s k x y)). Qed.
Lemma lem4411612 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term227 _106189 K s k x y) = (term265 _106189 K s k x y).
Proof. exact (TRANS (@lem4411591 _106189 K s k x y) (@lem4411611 _106189 K s k x y)). Qed.
Lemma lem4411613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411614 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term230 _106189 K s k x y) = (term266 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411613) (@lem4411612 _106189 K s k x y)). Qed.
Lemma lem4411615 {_106189 K : Type'} (x : K -> _106189) (y : K -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411616 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term232 _106189 K s k x y) = (term267 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411614 _106189 K s k x y) (@lem4411615 _106189 K x y)). Qed.
Lemma lem4411618 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4411619 {K : Type'} (P : K -> Prop) (Q : Prop) : (term183 K P Q) = (term184 K P Q).
Proof. exact (@lem4411618 K P Q). Qed.
Lemma lem4411620 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term268 _106189 K s k x y) = (term269 _106189 K s k x y).
Proof. exact (@lem4411619 K (term264 _106189 K s k x y) (x = y)). Qed.
Lemma lem4411621 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term270 _106189 K s k x y i) = (term262 _106189 K s k x y i).
Proof. exact (eq_refl (term270 _106189 K s k x y i)). Qed.
Lemma lem4411622 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term271 _106189 K s k x y) = (term264 _106189 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411621 _106189 K s k x y i)). Qed.
Lemma lem4411623 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411624 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term272 _106189 K s k x y) = (term265 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411623 K) (@lem4411622 _106189 K s k x y)). Qed.
Lemma lem4411625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411626 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term273 _106189 K s k x y) = (term266 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411625) (@lem4411624 _106189 K s k x y)). Qed.
Lemma lem4411627 {_106189 K : Type'} (x : K -> _106189) (y : K -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411628 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term268 _106189 K s k x y) = (term267 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411626 _106189 K s k x y) (@lem4411627 _106189 K x y)). Qed.
Lemma lem4411629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411630 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term274 _106189 K s k x y) = (term275 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411629) (@lem4411628 _106189 K s k x y)). Qed.
Lemma lem4411631 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term270 _106189 K s k x y i) = (term262 _106189 K s k x y i).
Proof. exact (eq_refl (term270 _106189 K s k x y i)). Qed.
Lemma lem4411632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411633 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term276 _106189 K s k x y i) = (term277 _106189 K s k x y i).
Proof. exact (MK_COMB (@lem4411632) (@lem4411631 _106189 K s k x y i)). Qed.
Lemma lem4411634 {_106189 K : Type'} (x : K -> _106189) (y : K -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411635 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : K) (x : K -> _106189) (y : K -> _106189) : (term278 _106189 K s k i x y) = (term279 _106189 K s k i x y).
Proof. exact (MK_COMB (@lem4411633 _106189 K s k x y i) (@lem4411634 _106189 K x y)). Qed.
Lemma lem4411636 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term280 _106189 K s k x y) = (term281 _106189 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411635 _106189 K s k i x y)). Qed.
Lemma lem4411637 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411638 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term269 _106189 K s k x y) = (term282 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411637 K) (@lem4411636 _106189 K s k x y)). Qed.
Lemma lem4411639 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : ((term268 _106189 K s k x y) = (term269 _106189 K s k x y)) = ((term267 _106189 K s k x y) = (term282 _106189 K s k x y)).
Proof. exact (MK_COMB (@lem4411630 _106189 K s k x y) (@lem4411638 _106189 K s k x y)). Qed.
Lemma lem4411640 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term267 _106189 K s k x y) = (term282 _106189 K s k x y).
Proof. exact (EQ_MP (@lem4411639 _106189 K s k x y) (@lem4411620 _106189 K s k x y)). Qed.
Lemma lem4411641 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term232 _106189 K s k x y) = (term282 _106189 K s k x y).
Proof. exact (TRANS (@lem4411616 _106189 K s k x y) (@lem4411640 _106189 K s k x y)). Qed.
Lemma lem4411642 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term233 _106189 K s k x) = (term283 _106189 K s k x).
Proof. exact (fun_ext (fun y : K -> _106189 => @lem4411641 _106189 K s k x y)). Qed.
Lemma lem4411643 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411644 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term234 _106189 K s k x) = (term284 _106189 K s k x).
Proof. exact (MK_COMB (@lem4411643 _106189 K) (@lem4411642 _106189 K s k x)). Qed.
Lemma lem4411646 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411647 {_106189 K : Type'} (P : type799 _106189 K) : (term287 _106189 K P) = (term288 _106189 K P).
Proof. exact (@lem4411646 (K -> _106189) K P). Qed.
Lemma lem4411648 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term289 _106189 K s k x) = (term290 _106189 K s k x).
Proof. exact (@lem4411647 _106189 K (term291 _106189 K s k x)). Qed.
Lemma lem4411649 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term292 _106189 K s k x y) = (term281 _106189 K s k x y).
Proof. exact (eq_refl (term292 _106189 K s k x y)). Qed.
Lemma lem4411650 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411651 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) (i : K) : (term293 _106189 K s k x y i) = (term294 _106189 K s k x y i).
Proof. exact (MK_COMB (@lem4411649 _106189 K s k x y) (@lem4411650 K i)). Qed.
Lemma lem4411652 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : K) (x : K -> _106189) (y : K -> _106189) : (term294 _106189 K s k x y i) = (term279 _106189 K s k i x y).
Proof. exact (eq_refl (term294 _106189 K s k x y i)). Qed.
Lemma lem4411653 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : K) (x : K -> _106189) (y : K -> _106189) : (term293 _106189 K s k x y i) = (term279 _106189 K s k i x y).
Proof. exact (TRANS (@lem4411651 _106189 K s k x y i) (@lem4411652 _106189 K s k i x y)). Qed.
Lemma lem4411654 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term295 _106189 K s k x y) = (term281 _106189 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411653 _106189 K s k i x y)). Qed.
Lemma lem4411655 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411656 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term296 _106189 K s k x y) = (term282 _106189 K s k x y).
Proof. exact (MK_COMB (@lem4411655 K) (@lem4411654 _106189 K s k x y)). Qed.
Lemma lem4411657 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term297 _106189 K s k x) = (term283 _106189 K s k x).
Proof. exact (fun_ext (fun y : K -> _106189 => @lem4411656 _106189 K s k x y)). Qed.
Lemma lem4411658 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411659 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term289 _106189 K s k x) = (term284 _106189 K s k x).
Proof. exact (MK_COMB (@lem4411658 _106189 K) (@lem4411657 _106189 K s k x)). Qed.
Lemma lem4411660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411661 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term298 _106189 K s k x) = (term299 _106189 K s k x).
Proof. exact (MK_COMB (@lem4411660) (@lem4411659 _106189 K s k x)). Qed.
Lemma lem4411662 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (y : K -> _106189) : (term292 _106189 K s k x y) = (term281 _106189 K s k x y).
Proof. exact (eq_refl (term292 _106189 K s k x y)). Qed.
Lemma lem4411663 {_106189 K : Type'} (i : type803 _106189 K) (y : K -> _106189) : (i y) = (i y).
Proof. exact (eq_refl (i y)). Qed.
Lemma lem4411664 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (i : type803 _106189 K) (y : K -> _106189) : (term300 _106189 K s k x i y) = (term301 _106189 K s k x i y).
Proof. exact (MK_COMB (@lem4411662 _106189 K s k x y) (@lem4411663 _106189 K i y)). Qed.
Lemma lem4411665 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type803 _106189 K) (x : K -> _106189) (y : K -> _106189) : (term301 _106189 K s k x i y) = (term302 _106189 K s k i x y).
Proof. exact (eq_refl (term301 _106189 K s k x i y)). Qed.
Lemma lem4411666 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type803 _106189 K) (x : K -> _106189) (y : K -> _106189) : (term300 _106189 K s k x i y) = (term302 _106189 K s k i x y).
Proof. exact (TRANS (@lem4411664 _106189 K s k x i y) (@lem4411665 _106189 K s k i x y)). Qed.
Lemma lem4411667 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type803 _106189 K) (x : K -> _106189) : (term303 _106189 K s k x i) = (term304 _106189 K s k i x).
Proof. exact (fun_ext (fun y : K -> _106189 => @lem4411666 _106189 K s k i x y)). Qed.
Lemma lem4411668 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411669 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type803 _106189 K) (x : K -> _106189) : (term305 _106189 K s k x i) = (term306 _106189 K s k i x).
Proof. exact (MK_COMB (@lem4411668 _106189 K) (@lem4411667 _106189 K s k i x)). Qed.
Lemma lem4411670 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term307 _106189 K s k x) = (term308 _106189 K s k x).
Proof. exact (fun_ext (fun i : type803 _106189 K => @lem4411669 _106189 K s k i x)). Qed.
Lemma lem4411671 {_106189 K : Type'} : (@ex ((K -> _106189) -> K)) = (@ex ((K -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106189) -> K))). Qed.
Lemma lem4411672 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term290 _106189 K s k x) = (term309 _106189 K s k x).
Proof. exact (MK_COMB (@lem4411671 _106189 K) (@lem4411670 _106189 K s k x)). Qed.
Lemma lem4411673 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : ((term289 _106189 K s k x) = (term290 _106189 K s k x)) = ((term284 _106189 K s k x) = (term309 _106189 K s k x)).
Proof. exact (MK_COMB (@lem4411661 _106189 K s k x) (@lem4411672 _106189 K s k x)). Qed.
Lemma lem4411674 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term284 _106189 K s k x) = (term309 _106189 K s k x).
Proof. exact (EQ_MP (@lem4411673 _106189 K s k x) (@lem4411648 _106189 K s k x)). Qed.
Lemma lem4411675 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term234 _106189 K s k x) = (term309 _106189 K s k x).
Proof. exact (TRANS (@lem4411644 _106189 K s k x) (@lem4411674 _106189 K s k x)). Qed.
Lemma lem4411676 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term235 _106189 K s k) = (term310 _106189 K s k).
Proof. exact (fun_ext (fun x : K -> _106189 => @lem4411675 _106189 K s k x)). Qed.
Lemma lem4411677 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411678 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term236 _106189 K s k) = (term311 _106189 K s k).
Proof. exact (MK_COMB (@lem4411677 _106189 K) (@lem4411676 _106189 K s k)). Qed.
Lemma lem4411680 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411681 {_106189 K : Type'} (P : type772 _106189 K) : (term312 _106189 K P) = (term313 _106189 K P).
Proof. exact (@lem4411680 (K -> _106189) (type803 _106189 K) P). Qed.
Lemma lem4411682 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term314 _106189 K s k) = (term315 _106189 K s k).
Proof. exact (@lem4411681 _106189 K (term316 _106189 K s k)). Qed.
Lemma lem4411683 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term317 _106189 K s k x) = (term308 _106189 K s k x).
Proof. exact (eq_refl (term317 _106189 K s k x)). Qed.
Lemma lem4411684 {_106189 K : Type'} (i : type803 _106189 K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411685 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) (i : type803 _106189 K) : (term318 _106189 K s k x i) = (term319 _106189 K s k x i).
Proof. exact (MK_COMB (@lem4411683 _106189 K s k x) (@lem4411684 _106189 K i)). Qed.
Lemma lem4411686 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type803 _106189 K) (x : K -> _106189) : (term319 _106189 K s k x i) = (term306 _106189 K s k i x).
Proof. exact (eq_refl (term319 _106189 K s k x i)). Qed.
Lemma lem4411687 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type803 _106189 K) (x : K -> _106189) : (term318 _106189 K s k x i) = (term306 _106189 K s k i x).
Proof. exact (TRANS (@lem4411685 _106189 K s k x i) (@lem4411686 _106189 K s k i x)). Qed.
Lemma lem4411688 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term320 _106189 K s k x) = (term308 _106189 K s k x).
Proof. exact (fun_ext (fun i : type803 _106189 K => @lem4411687 _106189 K s k i x)). Qed.
Lemma lem4411689 {_106189 K : Type'} : (@ex ((K -> _106189) -> K)) = (@ex ((K -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106189) -> K))). Qed.
Lemma lem4411690 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term321 _106189 K s k x) = (term309 _106189 K s k x).
Proof. exact (MK_COMB (@lem4411689 _106189 K) (@lem4411688 _106189 K s k x)). Qed.
Lemma lem4411691 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term322 _106189 K s k) = (term310 _106189 K s k).
Proof. exact (fun_ext (fun x : K -> _106189 => @lem4411690 _106189 K s k x)). Qed.
Lemma lem4411692 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411693 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term314 _106189 K s k) = (term311 _106189 K s k).
Proof. exact (MK_COMB (@lem4411692 _106189 K) (@lem4411691 _106189 K s k)). Qed.
Lemma lem4411694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411695 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term323 _106189 K s k) = (term324 _106189 K s k).
Proof. exact (MK_COMB (@lem4411694) (@lem4411693 _106189 K s k)). Qed.
Lemma lem4411696 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (x : K -> _106189) : (term317 _106189 K s k x) = (term308 _106189 K s k x).
Proof. exact (eq_refl (term317 _106189 K s k x)). Qed.
Lemma lem4411697 {_106189 K : Type'} (i : type785 _106189 K) (x : K -> _106189) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem4411698 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) (x : K -> _106189) : (term325 _106189 K s k i x) = (term326 _106189 K s k i x).
Proof. exact (MK_COMB (@lem4411696 _106189 K s k x) (@lem4411697 _106189 K i x)). Qed.
Lemma lem4411699 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) (x : K -> _106189) : (term326 _106189 K s k i x) = (term327 _106189 K s k i x).
Proof. exact (eq_refl (term326 _106189 K s k i x)). Qed.
Lemma lem4411700 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) (x : K -> _106189) : (term325 _106189 K s k i x) = (term327 _106189 K s k i x).
Proof. exact (TRANS (@lem4411698 _106189 K s k i x) (@lem4411699 _106189 K s k i x)). Qed.
Lemma lem4411701 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) : (term328 _106189 K s k i) = (term329 _106189 K s k i).
Proof. exact (fun_ext (fun x : K -> _106189 => @lem4411700 _106189 K s k i x)). Qed.
Lemma lem4411702 {_106189 K : Type'} : (@all (K -> _106189)) = (@all (K -> _106189)).
Proof. exact (eq_refl (@all (K -> _106189))). Qed.
Lemma lem4411703 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) : (term330 _106189 K s k i) = (term331 _106189 K s k i).
Proof. exact (MK_COMB (@lem4411702 _106189 K) (@lem4411701 _106189 K s k i)). Qed.
Lemma lem4411704 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term332 _106189 K s k) = (term333 _106189 K s k).
Proof. exact (fun_ext (fun i : type785 _106189 K => @lem4411703 _106189 K s k i)). Qed.
Lemma lem4411705 {_106189 K : Type'} : (@ex ((K -> _106189) -> (K -> _106189) -> K)) = (@ex ((K -> _106189) -> (K -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106189) -> (K -> _106189) -> K))). Qed.
Lemma lem4411706 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term315 _106189 K s k) = (term334 _106189 K s k).
Proof. exact (MK_COMB (@lem4411705 _106189 K) (@lem4411704 _106189 K s k)). Qed.
Lemma lem4411707 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : ((term314 _106189 K s k) = (term315 _106189 K s k)) = ((term311 _106189 K s k) = (term334 _106189 K s k)).
Proof. exact (MK_COMB (@lem4411695 _106189 K s k) (@lem4411706 _106189 K s k)). Qed.
Lemma lem4411708 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term311 _106189 K s k) = (term334 _106189 K s k).
Proof. exact (EQ_MP (@lem4411707 _106189 K s k) (@lem4411682 _106189 K s k)). Qed.
Lemma lem4411709 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term236 _106189 K s k) = (term334 _106189 K s k).
Proof. exact (TRANS (@lem4411678 _106189 K s k) (@lem4411708 _106189 K s k)). Qed.
Lemma lem4411710 {_106189 K : Type'} (k : K -> Prop) : (term237 _106189 K k) = (term335 _106189 K k).
Proof. exact (fun_ext (fun s : type1470 _106189 K => @lem4411709 _106189 K s k)). Qed.
Lemma lem4411711 {_106189 K : Type'} : (@all (K -> _106189 -> Prop)) = (@all (K -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (K -> _106189 -> Prop))). Qed.
Lemma lem4411712 {_106189 K : Type'} (k : K -> Prop) : (term238 _106189 K k) = (term336 _106189 K k).
Proof. exact (MK_COMB (@lem4411711 _106189 K) (@lem4411710 _106189 K k)). Qed.
Lemma lem4411714 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411715 {_106189 K : Type'} (P : type729 _106189 K) : (term337 _106189 K P) = (term338 _106189 K P).
Proof. exact (@lem4411714 (type1470 _106189 K) (type785 _106189 K) P). Qed.
Lemma lem4411716 {_106189 K : Type'} (k : K -> Prop) : (term339 _106189 K k) = (term340 _106189 K k).
Proof. exact (@lem4411715 _106189 K (term341 _106189 K k)). Qed.
Lemma lem4411717 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term342 _106189 K k s) = (term333 _106189 K s k).
Proof. exact (eq_refl (term342 _106189 K k s)). Qed.
Lemma lem4411718 {_106189 K : Type'} (i : type785 _106189 K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411719 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) : (term343 _106189 K k s i) = (term344 _106189 K s k i).
Proof. exact (MK_COMB (@lem4411717 _106189 K s k) (@lem4411718 _106189 K i)). Qed.
Lemma lem4411720 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) : (term344 _106189 K s k i) = (term331 _106189 K s k i).
Proof. exact (eq_refl (term344 _106189 K s k i)). Qed.
Lemma lem4411721 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) (i : type785 _106189 K) : (term343 _106189 K k s i) = (term331 _106189 K s k i).
Proof. exact (TRANS (@lem4411719 _106189 K s k i) (@lem4411720 _106189 K s k i)). Qed.
Lemma lem4411722 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term345 _106189 K k s) = (term333 _106189 K s k).
Proof. exact (fun_ext (fun i : type785 _106189 K => @lem4411721 _106189 K s k i)). Qed.
Lemma lem4411723 {_106189 K : Type'} : (@ex ((K -> _106189) -> (K -> _106189) -> K)) = (@ex ((K -> _106189) -> (K -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106189) -> (K -> _106189) -> K))). Qed.
Lemma lem4411724 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term346 _106189 K k s) = (term334 _106189 K s k).
Proof. exact (MK_COMB (@lem4411723 _106189 K) (@lem4411722 _106189 K s k)). Qed.
Lemma lem4411725 {_106189 K : Type'} (k : K -> Prop) : (term347 _106189 K k) = (term335 _106189 K k).
Proof. exact (fun_ext (fun s : type1470 _106189 K => @lem4411724 _106189 K s k)). Qed.
Lemma lem4411726 {_106189 K : Type'} : (@all (K -> _106189 -> Prop)) = (@all (K -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (K -> _106189 -> Prop))). Qed.
Lemma lem4411727 {_106189 K : Type'} (k : K -> Prop) : (term339 _106189 K k) = (term336 _106189 K k).
Proof. exact (MK_COMB (@lem4411726 _106189 K) (@lem4411725 _106189 K k)). Qed.
Lemma lem4411728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411729 {_106189 K : Type'} (k : K -> Prop) : (term348 _106189 K k) = (term349 _106189 K k).
Proof. exact (MK_COMB (@lem4411728) (@lem4411727 _106189 K k)). Qed.
Lemma lem4411730 {_106189 K : Type'} (s : type1470 _106189 K) (k : K -> Prop) : (term342 _106189 K k s) = (term333 _106189 K s k).
Proof. exact (eq_refl (term342 _106189 K k s)). Qed.
Lemma lem4411731 {_106189 K : Type'} (i : type733 _106189 K) (s : type1470 _106189 K) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem4411732 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) (s : type1470 _106189 K) : (term350 _106189 K k i s) = (term351 _106189 K k i s).
Proof. exact (MK_COMB (@lem4411730 _106189 K s k) (@lem4411731 _106189 K i s)). Qed.
Lemma lem4411733 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) (s : type1470 _106189 K) : (term351 _106189 K k i s) = (term352 _106189 K k i s).
Proof. exact (eq_refl (term351 _106189 K k i s)). Qed.
Lemma lem4411734 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) (s : type1470 _106189 K) : (term350 _106189 K k i s) = (term352 _106189 K k i s).
Proof. exact (TRANS (@lem4411732 _106189 K k i s) (@lem4411733 _106189 K k i s)). Qed.
Lemma lem4411735 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) : (term353 _106189 K k i) = (term354 _106189 K k i).
Proof. exact (fun_ext (fun s : type1470 _106189 K => @lem4411734 _106189 K k i s)). Qed.
Lemma lem4411736 {_106189 K : Type'} : (@all (K -> _106189 -> Prop)) = (@all (K -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (K -> _106189 -> Prop))). Qed.
Lemma lem4411737 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) : (term355 _106189 K k i) = (term356 _106189 K k i).
Proof. exact (MK_COMB (@lem4411736 _106189 K) (@lem4411735 _106189 K k i)). Qed.
Lemma lem4411738 {_106189 K : Type'} (k : K -> Prop) : (term357 _106189 K k) = (term358 _106189 K k).
Proof. exact (fun_ext (fun i : type733 _106189 K => @lem4411737 _106189 K k i)). Qed.
Lemma lem4411739 {_106189 K : Type'} : (@ex ((K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K)) = (@ex ((K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K))). Qed.
Lemma lem4411740 {_106189 K : Type'} (k : K -> Prop) : (term340 _106189 K k) = (term359 _106189 K k).
Proof. exact (MK_COMB (@lem4411739 _106189 K) (@lem4411738 _106189 K k)). Qed.
Lemma lem4411741 {_106189 K : Type'} (k : K -> Prop) : ((term339 _106189 K k) = (term340 _106189 K k)) = ((term336 _106189 K k) = (term359 _106189 K k)).
Proof. exact (MK_COMB (@lem4411729 _106189 K k) (@lem4411740 _106189 K k)). Qed.
Lemma lem4411742 {_106189 K : Type'} (k : K -> Prop) : (term336 _106189 K k) = (term359 _106189 K k).
Proof. exact (EQ_MP (@lem4411741 _106189 K k) (@lem4411716 _106189 K k)). Qed.
Lemma lem4411743 {_106189 K : Type'} (k : K -> Prop) : (term238 _106189 K k) = (term359 _106189 K k).
Proof. exact (TRANS (@lem4411712 _106189 K k) (@lem4411742 _106189 K k)). Qed.
Lemma lem4411744 {_106189 K : Type'} : (term239 _106189 K) = (term360 _106189 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4411743 _106189 K k)). Qed.
Lemma lem4411745 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4411746 {_106189 K : Type'} : (term240 _106189 K) = (term361 _106189 K).
Proof. exact (MK_COMB (@lem4411745 K) (@lem4411744 _106189 K)). Qed.
Lemma lem4411748 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4411749 {_106189 K : Type'} (P : type824 _106189 K) : (term362 _106189 K P) = (term363 _106189 K P).
Proof. exact (@lem4411748 (K -> Prop) (type733 _106189 K) P). Qed.
Lemma lem4411750 {_106189 K : Type'} : (term364 _106189 K) = (term365 _106189 K).
Proof. exact (@lem4411749 _106189 K (term366 _106189 K)). Qed.
Lemma lem4411751 {_106189 K : Type'} (k : K -> Prop) : (term367 _106189 K k) = (term358 _106189 K k).
Proof. exact (eq_refl (term367 _106189 K k)). Qed.
Lemma lem4411752 {_106189 K : Type'} (i : type733 _106189 K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4411753 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) : (term368 _106189 K k i) = (term369 _106189 K k i).
Proof. exact (MK_COMB (@lem4411751 _106189 K k) (@lem4411752 _106189 K i)). Qed.
Lemma lem4411754 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) : (term369 _106189 K k i) = (term356 _106189 K k i).
Proof. exact (eq_refl (term369 _106189 K k i)). Qed.
Lemma lem4411755 {_106189 K : Type'} (k : K -> Prop) (i : type733 _106189 K) : (term368 _106189 K k i) = (term356 _106189 K k i).
Proof. exact (TRANS (@lem4411753 _106189 K k i) (@lem4411754 _106189 K k i)). Qed.
Lemma lem4411756 {_106189 K : Type'} (k : K -> Prop) : (term370 _106189 K k) = (term358 _106189 K k).
Proof. exact (fun_ext (fun i : type733 _106189 K => @lem4411755 _106189 K k i)). Qed.
Lemma lem4411757 {_106189 K : Type'} : (@ex ((K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K)) = (@ex ((K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K))). Qed.
Lemma lem4411758 {_106189 K : Type'} (k : K -> Prop) : (term371 _106189 K k) = (term359 _106189 K k).
Proof. exact (MK_COMB (@lem4411757 _106189 K) (@lem4411756 _106189 K k)). Qed.
Lemma lem4411759 {_106189 K : Type'} : (term372 _106189 K) = (term360 _106189 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4411758 _106189 K k)). Qed.
Lemma lem4411760 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4411761 {_106189 K : Type'} : (term364 _106189 K) = (term361 _106189 K).
Proof. exact (MK_COMB (@lem4411760 K) (@lem4411759 _106189 K)). Qed.
Lemma lem4411762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411763 {_106189 K : Type'} : (term373 _106189 K) = (term374 _106189 K).
Proof. exact (MK_COMB (@lem4411762) (@lem4411761 _106189 K)). Qed.
Lemma lem4411764 {_106189 K : Type'} (k : K -> Prop) : (term367 _106189 K k) = (term358 _106189 K k).
Proof. exact (eq_refl (term367 _106189 K k)). Qed.
Lemma lem4411765 {_106189 K : Type'} (i : type844 _106189 K) (k : K -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem4411766 {_106189 K : Type'} (i : type844 _106189 K) (k : K -> Prop) : (term375 _106189 K i k) = (term376 _106189 K i k).
Proof. exact (MK_COMB (@lem4411764 _106189 K k) (@lem4411765 _106189 K i k)). Qed.
Lemma lem4411767 {_106189 K : Type'} (i : type844 _106189 K) (k : K -> Prop) : (term376 _106189 K i k) = (term377 _106189 K i k).
Proof. exact (eq_refl (term376 _106189 K i k)). Qed.
Lemma lem4411768 {_106189 K : Type'} (i : type844 _106189 K) (k : K -> Prop) : (term375 _106189 K i k) = (term377 _106189 K i k).
Proof. exact (TRANS (@lem4411766 _106189 K i k) (@lem4411767 _106189 K i k)). Qed.
Lemma lem4411769 {_106189 K : Type'} (i : type844 _106189 K) : (term378 _106189 K i) = (term379 _106189 K i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4411768 _106189 K i k)). Qed.
Lemma lem4411770 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4411771 {_106189 K : Type'} (i : type844 _106189 K) : (term380 _106189 K i) = (term381 _106189 K i).
Proof. exact (MK_COMB (@lem4411770 K) (@lem4411769 _106189 K i)). Qed.
Lemma lem4411772 {_106189 K : Type'} : (term382 _106189 K) = (term383 _106189 K).
Proof. exact (fun_ext (fun i : type844 _106189 K => @lem4411771 _106189 K i)). Qed.
Lemma lem4411773 {_106189 K : Type'} : (@ex ((K -> Prop) -> (K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K)) = (@ex ((K -> Prop) -> (K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> _106189 -> Prop) -> (K -> _106189) -> (K -> _106189) -> K))). Qed.
Lemma lem4411774 {_106189 K : Type'} : (term365 _106189 K) = (term384 _106189 K).
Proof. exact (MK_COMB (@lem4411773 _106189 K) (@lem4411772 _106189 K)). Qed.
Lemma lem4411775 {_106189 K : Type'} : ((term364 _106189 K) = (term365 _106189 K)) = ((term361 _106189 K) = (term384 _106189 K)).
Proof. exact (MK_COMB (@lem4411763 _106189 K) (@lem4411774 _106189 K)). Qed.
Lemma lem4411776 {_106189 K : Type'} : (term361 _106189 K) = (term384 _106189 K).
Proof. exact (EQ_MP (@lem4411775 _106189 K) (@lem4411750 _106189 K)). Qed.
Lemma lem4411778 {_106189 K : Type'} : (term240 _106189 K) = (term384 _106189 K).
Proof. exact (TRANS (@lem4411746 _106189 K) (@lem4411776 _106189 K)). Qed.
Lemma lem4411779 {_106189 K : Type'} : (term11 _106189 K) = (term384 _106189 K).
Proof. exact (TRANS (@lem4411460 _106189 K) (@lem4411778 _106189 K)). Qed.
Lemma lem4411780 {_106189 K : Type'} (h1 : term11 _106189 K) : term384 _106189 K.
Proof. exact (EQ_MP (@lem4411779 _106189 K) (@lem4410343 _106189 K h1)). Qed.
Lemma lem4411789 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term557 _106189 _106193 K k x y i) = (term558 _106189 _106193 K k x y i).
Proof. exact (@lem17362 (@IN K i k) ((x i) = (y i))). Qed.
Lemma lem4411790 {K : Type'} (P : K -> Prop) : (term107 K P) = (term108 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4411791 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term559 _106189 _106193 K k x y) = (term560 _106189 _106193 K k x y).
Proof. exact (@lem4411790 K (term50 _106189 _106193 K k x y)). Qed.
Lemma lem4411792 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term561 _106189 _106193 K k x y i) = (term49 _106189 _106193 K k x y i).
Proof. exact (eq_refl (term561 _106189 _106193 K k x y i)). Qed.
Lemma lem4411793 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4411794 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term562 _106189 _106193 K k x y i) = (term557 _106189 _106193 K k x y i).
Proof. exact (MK_COMB (@lem4411793) (@lem4411792 _106189 _106193 K k x y i)). Qed.
Lemma lem4411795 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term562 _106189 _106193 K k x y i) = (term558 _106189 _106193 K k x y i).
Proof. exact (TRANS (@lem4411794 _106189 _106193 K k x y i) (@lem4411789 _106189 _106193 K k x y i)). Qed.
Lemma lem4411796 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term563 _106189 _106193 K k x y) = (term564 _106189 _106193 K k x y).
Proof. exact (fun_ext (fun i : K => @lem4411795 _106189 _106193 K k x y i)). Qed.
Lemma lem4411797 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411798 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term560 _106189 _106193 K k x y) = (term565 _106189 _106193 K k x y).
Proof. exact (MK_COMB (@lem4411797 K) (@lem4411796 _106189 _106193 K k x y)). Qed.
Lemma lem4411799 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term559 _106189 _106193 K k x y) = (term565 _106189 _106193 K k x y).
Proof. exact (TRANS (@lem4411791 _106189 _106193 K k x y) (@lem4411798 _106189 _106193 K k x y)). Qed.
Lemma lem4411801 {_106189 _106193 K : Type'} (y : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term566 _106189 _106193 K y k s) = (term566 _106189 _106193 K y k s).
Proof. exact (eq_refl (term566 _106189 _106193 K y k s)). Qed.
Lemma lem4411802 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term567 _106189 _106193 K s k x y) = (term568 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411801 _106189 _106193 K y k s) (@lem4411799 _106189 _106193 K k x y)). Qed.
Lemma lem4411803 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term569 _106189 _106193 K s k x y) = (term567 _106189 _106193 K s k x y).
Proof. exact (@lem17045 (term570 _106189 _106193 K y k s) (term51 _106189 _106193 K k x y)). Qed.
Lemma lem4411804 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term569 _106189 _106193 K s k x y) = (term568 _106189 _106193 K s k x y).
Proof. exact (TRANS (@lem4411803 _106189 _106193 K s k x y) (@lem4411802 _106189 _106193 K s k x y)). Qed.
Lemma lem4411806 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term566 _106189 _106193 K x k s) = (term566 _106189 _106193 K x k s).
Proof. exact (eq_refl (term566 _106189 _106193 K x k s)). Qed.
Lemma lem4411807 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term571 _106189 _106193 K s k x y) = (term572 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411806 _106189 _106193 K x k s) (@lem4411804 _106189 _106193 K s k x y)). Qed.
Lemma lem4411808 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term573 _106189 _106193 K s k x y) = (term571 _106189 _106193 K s k x y).
Proof. exact (@lem17045 (term570 _106189 _106193 K x k s) (term53 _106189 _106193 K s k x y)). Qed.
Lemma lem4411809 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term573 _106189 _106193 K s k x y) = (term572 _106189 _106193 K s k x y).
Proof. exact (TRANS (@lem4411808 _106189 _106193 K s k x y) (@lem4411807 _106189 _106193 K s k x y)). Qed.
Lemma lem4411810 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411812 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term574 _106189 _106193 K s k x y) = (term575 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411811) (@lem4411809 _106189 _106193 K s k x y)). Qed.
Lemma lem4411813 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term576 _106189 _106193 K s k x y) = (term577 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411812 _106189 _106193 K s k x y) (@lem4411810 _106189 _106193 K x y)). Qed.
Lemma lem4411814 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term56 _106189 _106193 K s k x y) = (term576 _106189 _106193 K s k x y).
Proof. exact (@lem17265 (term54 _106189 _106193 K s k x y) (x = y)). Qed.
Lemma lem4411815 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term56 _106189 _106193 K s k x y) = (term577 _106189 _106193 K s k x y).
Proof. exact (TRANS (@lem4411814 _106189 _106193 K s k x y) (@lem4411813 _106189 _106193 K s k x y)). Qed.
Lemma lem4411816 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term57 _106189 _106193 K s k x) = (term578 _106189 _106193 K s k x).
Proof. exact (fun_ext (fun y : type1518 _106189 _106193 K => @lem4411815 _106189 _106193 K s k x y)). Qed.
Lemma lem4411817 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4411818 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term58 _106189 _106193 K s k x) = (term579 _106189 _106193 K s k x).
Proof. exact (MK_COMB (@lem4411817 _106189 _106193 K) (@lem4411816 _106189 _106193 K s k x)). Qed.
Lemma lem4411819 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term59 _106189 _106193 K s k) = (term580 _106189 _106193 K s k).
Proof. exact (fun_ext (fun x : type1518 _106189 _106193 K => @lem4411818 _106189 _106193 K s k x)). Qed.
Lemma lem4411820 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4411821 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term60 _106189 _106193 K s k) = (term581 _106189 _106193 K s k).
Proof. exact (MK_COMB (@lem4411820 _106189 _106193 K) (@lem4411819 _106189 _106193 K s k)). Qed.
Lemma lem4411822 {_106189 _106193 K : Type'} (k : K -> Prop) : (term61 _106189 _106193 K k) = (term582 _106189 _106193 K k).
Proof. exact (fun_ext (fun s : type1508 _106189 _106193 K => @lem4411821 _106189 _106193 K s k)). Qed.
Lemma lem4411823 {_106189 _106193 K : Type'} : (@all (K -> (_106193 -> _106189) -> Prop)) = (@all (K -> (_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all (K -> (_106193 -> _106189) -> Prop))). Qed.
Lemma lem4411824 {_106189 _106193 K : Type'} (k : K -> Prop) : (term62 _106189 _106193 K k) = (term583 _106189 _106193 K k).
Proof. exact (MK_COMB (@lem4411823 _106189 _106193 K) (@lem4411822 _106189 _106193 K k)). Qed.
Lemma lem4411825 {_106189 _106193 K : Type'} : (term63 _106189 _106193 K) = (term584 _106189 _106193 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4411824 _106189 _106193 K k)). Qed.
Lemma lem4411826 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4411827 {_106189 _106193 K : Type'} : (term14 _106189 _106193 K) = (term585 _106189 _106193 K).
Proof. exact (MK_COMB (@lem4411826 K) (@lem4411825 _106189 _106193 K)). Qed.
Lemma lem4411938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4411939 {K : Type'} (P : Prop) (Q : K -> Prop) : (term241 K P Q) = (term242 K P Q).
Proof. exact (@lem4411938 K P Q). Qed.
Lemma lem4411940 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term586 _106189 _106193 K s k x y) = (term587 _106189 _106193 K s k x y).
Proof. exact (@lem4411939 K (term588 _106189 _106193 K y k s) (term564 _106189 _106193 K k x y)). Qed.
Lemma lem4411941 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term589 _106189 _106193 K k x y i) = (term558 _106189 _106193 K k x y i).
Proof. exact (eq_refl (term589 _106189 _106193 K k x y i)). Qed.
Lemma lem4411942 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term590 _106189 _106193 K k x y) = (term564 _106189 _106193 K k x y).
Proof. exact (fun_ext (fun i : K => @lem4411941 _106189 _106193 K k x y i)). Qed.
Lemma lem4411943 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411944 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term591 _106189 _106193 K k x y) = (term565 _106189 _106193 K k x y).
Proof. exact (MK_COMB (@lem4411943 K) (@lem4411942 _106189 _106193 K k x y)). Qed.
Lemma lem4411945 {_106189 _106193 K : Type'} (y : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term566 _106189 _106193 K y k s) = (term566 _106189 _106193 K y k s).
Proof. exact (eq_refl (term566 _106189 _106193 K y k s)). Qed.
Lemma lem4411946 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term586 _106189 _106193 K s k x y) = (term568 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411945 _106189 _106193 K y k s) (@lem4411944 _106189 _106193 K k x y)). Qed.
Lemma lem4411947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411948 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term592 _106189 _106193 K s k x y) = (term593 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411947) (@lem4411946 _106189 _106193 K s k x y)). Qed.
Lemma lem4411949 {_106189 _106193 K : Type'} (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term589 _106189 _106193 K k x y i) = (term558 _106189 _106193 K k x y i).
Proof. exact (eq_refl (term589 _106189 _106193 K k x y i)). Qed.
Lemma lem4411950 {_106189 _106193 K : Type'} (y : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term566 _106189 _106193 K y k s) = (term566 _106189 _106193 K y k s).
Proof. exact (eq_refl (term566 _106189 _106193 K y k s)). Qed.
Lemma lem4411951 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term594 _106189 _106193 K s k x y i) = (term595 _106189 _106193 K s k x y i).
Proof. exact (MK_COMB (@lem4411950 _106189 _106193 K y k s) (@lem4411949 _106189 _106193 K k x y i)). Qed.
Lemma lem4411952 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term596 _106189 _106193 K s k x y) = (term597 _106189 _106193 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411951 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411953 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411954 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term587 _106189 _106193 K s k x y) = (term598 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411953 K) (@lem4411952 _106189 _106193 K s k x y)). Qed.
Lemma lem4411955 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : ((term586 _106189 _106193 K s k x y) = (term587 _106189 _106193 K s k x y)) = ((term568 _106189 _106193 K s k x y) = (term598 _106189 _106193 K s k x y)).
Proof. exact (MK_COMB (@lem4411948 _106189 _106193 K s k x y) (@lem4411954 _106189 _106193 K s k x y)). Qed.
Lemma lem4411956 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term568 _106189 _106193 K s k x y) = (term598 _106189 _106193 K s k x y).
Proof. exact (EQ_MP (@lem4411955 _106189 _106193 K s k x y) (@lem4411940 _106189 _106193 K s k x y)). Qed.
Lemma lem4411957 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term566 _106189 _106193 K x k s) = (term566 _106189 _106193 K x k s).
Proof. exact (eq_refl (term566 _106189 _106193 K x k s)). Qed.
Lemma lem4411958 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term572 _106189 _106193 K s k x y) = (term599 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411957 _106189 _106193 K x k s) (@lem4411956 _106189 _106193 K s k x y)). Qed.
Lemma lem4411960 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4411961 {K : Type'} (P : Prop) (Q : K -> Prop) : (term241 K P Q) = (term242 K P Q).
Proof. exact (@lem4411960 K P Q). Qed.
Lemma lem4411962 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term600 _106189 _106193 K s k x y) = (term601 _106189 _106193 K s k x y).
Proof. exact (@lem4411961 K (term588 _106189 _106193 K x k s) (term597 _106189 _106193 K s k x y)). Qed.
Lemma lem4411963 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term602 _106189 _106193 K s k x y i) = (term595 _106189 _106193 K s k x y i).
Proof. exact (eq_refl (term602 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411964 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term603 _106189 _106193 K s k x y) = (term597 _106189 _106193 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411963 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411965 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411966 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term604 _106189 _106193 K s k x y) = (term598 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411965 K) (@lem4411964 _106189 _106193 K s k x y)). Qed.
Lemma lem4411967 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term566 _106189 _106193 K x k s) = (term566 _106189 _106193 K x k s).
Proof. exact (eq_refl (term566 _106189 _106193 K x k s)). Qed.
Lemma lem4411968 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term600 _106189 _106193 K s k x y) = (term599 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411967 _106189 _106193 K x k s) (@lem4411966 _106189 _106193 K s k x y)). Qed.
Lemma lem4411969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411970 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term605 _106189 _106193 K s k x y) = (term606 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411969) (@lem4411968 _106189 _106193 K s k x y)). Qed.
Lemma lem4411971 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term602 _106189 _106193 K s k x y i) = (term595 _106189 _106193 K s k x y i).
Proof. exact (eq_refl (term602 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411972 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (k : K -> Prop) (s : type1508 _106189 _106193 K) : (term566 _106189 _106193 K x k s) = (term566 _106189 _106193 K x k s).
Proof. exact (eq_refl (term566 _106189 _106193 K x k s)). Qed.
Lemma lem4411973 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term607 _106189 _106193 K s k x y i) = (term608 _106189 _106193 K s k x y i).
Proof. exact (MK_COMB (@lem4411972 _106189 _106193 K x k s) (@lem4411971 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411974 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term609 _106189 _106193 K s k x y) = (term610 _106189 _106193 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411973 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411975 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411976 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term601 _106189 _106193 K s k x y) = (term611 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411975 K) (@lem4411974 _106189 _106193 K s k x y)). Qed.
Lemma lem4411977 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : ((term600 _106189 _106193 K s k x y) = (term601 _106189 _106193 K s k x y)) = ((term599 _106189 _106193 K s k x y) = (term611 _106189 _106193 K s k x y)).
Proof. exact (MK_COMB (@lem4411970 _106189 _106193 K s k x y) (@lem4411976 _106189 _106193 K s k x y)). Qed.
Lemma lem4411978 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term599 _106189 _106193 K s k x y) = (term611 _106189 _106193 K s k x y).
Proof. exact (EQ_MP (@lem4411977 _106189 _106193 K s k x y) (@lem4411962 _106189 _106193 K s k x y)). Qed.
Lemma lem4411979 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term572 _106189 _106193 K s k x y) = (term611 _106189 _106193 K s k x y).
Proof. exact (TRANS (@lem4411958 _106189 _106193 K s k x y) (@lem4411978 _106189 _106193 K s k x y)). Qed.
Lemma lem4411980 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411981 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term575 _106189 _106193 K s k x y) = (term612 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411980) (@lem4411979 _106189 _106193 K s k x y)). Qed.
Lemma lem4411982 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411983 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term577 _106189 _106193 K s k x y) = (term613 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411981 _106189 _106193 K s k x y) (@lem4411982 _106189 _106193 K x y)). Qed.
Lemma lem4411985 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4411986 {K : Type'} (P : K -> Prop) (Q : Prop) : (term183 K P Q) = (term184 K P Q).
Proof. exact (@lem4411985 K P Q). Qed.
Lemma lem4411987 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term614 _106189 _106193 K s k x y) = (term615 _106189 _106193 K s k x y).
Proof. exact (@lem4411986 K (term610 _106189 _106193 K s k x y) (x = y)). Qed.
Lemma lem4411988 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term616 _106189 _106193 K s k x y i) = (term608 _106189 _106193 K s k x y i).
Proof. exact (eq_refl (term616 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411989 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term617 _106189 _106193 K s k x y) = (term610 _106189 _106193 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4411988 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411990 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4411991 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term618 _106189 _106193 K s k x y) = (term611 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411990 K) (@lem4411989 _106189 _106193 K s k x y)). Qed.
Lemma lem4411992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4411993 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term619 _106189 _106193 K s k x y) = (term612 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411992) (@lem4411991 _106189 _106193 K s k x y)). Qed.
Lemma lem4411994 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4411995 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term614 _106189 _106193 K s k x y) = (term613 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411993 _106189 _106193 K s k x y) (@lem4411994 _106189 _106193 K x y)). Qed.
Lemma lem4411996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4411997 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term620 _106189 _106193 K s k x y) = (term621 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4411996) (@lem4411995 _106189 _106193 K s k x y)). Qed.
Lemma lem4411998 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term616 _106189 _106193 K s k x y i) = (term608 _106189 _106193 K s k x y i).
Proof. exact (eq_refl (term616 _106189 _106193 K s k x y i)). Qed.
Lemma lem4411999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4412000 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term622 _106189 _106193 K s k x y i) = (term623 _106189 _106193 K s k x y i).
Proof. exact (MK_COMB (@lem4411999) (@lem4411998 _106189 _106193 K s k x y i)). Qed.
Lemma lem4412001 {_106189 _106193 K : Type'} (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4412002 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : K) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term624 _106189 _106193 K s k i x y) = (term625 _106189 _106193 K s k i x y).
Proof. exact (MK_COMB (@lem4412000 _106189 _106193 K s k x y i) (@lem4412001 _106189 _106193 K x y)). Qed.
Lemma lem4412003 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term626 _106189 _106193 K s k x y) = (term627 _106189 _106193 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4412002 _106189 _106193 K s k i x y)). Qed.
Lemma lem4412004 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4412005 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term615 _106189 _106193 K s k x y) = (term628 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4412004 K) (@lem4412003 _106189 _106193 K s k x y)). Qed.
Lemma lem4412006 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : ((term614 _106189 _106193 K s k x y) = (term615 _106189 _106193 K s k x y)) = ((term613 _106189 _106193 K s k x y) = (term628 _106189 _106193 K s k x y)).
Proof. exact (MK_COMB (@lem4411997 _106189 _106193 K s k x y) (@lem4412005 _106189 _106193 K s k x y)). Qed.
Lemma lem4412007 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term613 _106189 _106193 K s k x y) = (term628 _106189 _106193 K s k x y).
Proof. exact (EQ_MP (@lem4412006 _106189 _106193 K s k x y) (@lem4411987 _106189 _106193 K s k x y)). Qed.
Lemma lem4412008 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term577 _106189 _106193 K s k x y) = (term628 _106189 _106193 K s k x y).
Proof. exact (TRANS (@lem4411983 _106189 _106193 K s k x y) (@lem4412007 _106189 _106193 K s k x y)). Qed.
Lemma lem4412009 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term578 _106189 _106193 K s k x) = (term629 _106189 _106193 K s k x).
Proof. exact (fun_ext (fun y : type1518 _106189 _106193 K => @lem4412008 _106189 _106193 K s k x y)). Qed.
Lemma lem4412010 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4412011 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term579 _106189 _106193 K s k x) = (term630 _106189 _106193 K s k x).
Proof. exact (MK_COMB (@lem4412010 _106189 _106193 K) (@lem4412009 _106189 _106193 K s k x)). Qed.
Lemma lem4412013 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412014 {_106189 _106193 K : Type'} (P : type874 _106189 _106193 K) : (term631 _106189 _106193 K P) = (term632 _106189 _106193 K P).
Proof. exact (@lem4412013 (type1518 _106189 _106193 K) K P). Qed.
Lemma lem4412015 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term633 _106189 _106193 K s k x) = (term634 _106189 _106193 K s k x).
Proof. exact (@lem4412014 _106189 _106193 K (term635 _106189 _106193 K s k x)). Qed.
Lemma lem4412016 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term636 _106189 _106193 K s k x y) = (term627 _106189 _106193 K s k x y).
Proof. exact (eq_refl (term636 _106189 _106193 K s k x y)). Qed.
Lemma lem4412017 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412018 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) (i : K) : (term637 _106189 _106193 K s k x y i) = (term638 _106189 _106193 K s k x y i).
Proof. exact (MK_COMB (@lem4412016 _106189 _106193 K s k x y) (@lem4412017 K i)). Qed.
Lemma lem4412019 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : K) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term638 _106189 _106193 K s k x y i) = (term625 _106189 _106193 K s k i x y).
Proof. exact (eq_refl (term638 _106189 _106193 K s k x y i)). Qed.
Lemma lem4412020 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : K) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term637 _106189 _106193 K s k x y i) = (term625 _106189 _106193 K s k i x y).
Proof. exact (TRANS (@lem4412018 _106189 _106193 K s k x y i) (@lem4412019 _106189 _106193 K s k i x y)). Qed.
Lemma lem4412021 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term639 _106189 _106193 K s k x y) = (term627 _106189 _106193 K s k x y).
Proof. exact (fun_ext (fun i : K => @lem4412020 _106189 _106193 K s k i x y)). Qed.
Lemma lem4412022 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4412023 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term640 _106189 _106193 K s k x y) = (term628 _106189 _106193 K s k x y).
Proof. exact (MK_COMB (@lem4412022 K) (@lem4412021 _106189 _106193 K s k x y)). Qed.
Lemma lem4412024 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term641 _106189 _106193 K s k x) = (term629 _106189 _106193 K s k x).
Proof. exact (fun_ext (fun y : type1518 _106189 _106193 K => @lem4412023 _106189 _106193 K s k x y)). Qed.
Lemma lem4412025 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4412026 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term633 _106189 _106193 K s k x) = (term630 _106189 _106193 K s k x).
Proof. exact (MK_COMB (@lem4412025 _106189 _106193 K) (@lem4412024 _106189 _106193 K s k x)). Qed.
Lemma lem4412027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412028 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term642 _106189 _106193 K s k x) = (term643 _106189 _106193 K s k x).
Proof. exact (MK_COMB (@lem4412027) (@lem4412026 _106189 _106193 K s k x)). Qed.
Lemma lem4412029 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term636 _106189 _106193 K s k x y) = (term627 _106189 _106193 K s k x y).
Proof. exact (eq_refl (term636 _106189 _106193 K s k x y)). Qed.
Lemma lem4412030 {_106189 _106193 K : Type'} (i : type875 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (i y) = (i y).
Proof. exact (eq_refl (i y)). Qed.
Lemma lem4412031 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (i : type875 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term644 _106189 _106193 K s k x i y) = (term645 _106189 _106193 K s k x i y).
Proof. exact (MK_COMB (@lem4412029 _106189 _106193 K s k x y) (@lem4412030 _106189 _106193 K i y)). Qed.
Lemma lem4412032 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type875 _106189 _106193 K) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term645 _106189 _106193 K s k x i y) = (term646 _106189 _106193 K s k i x y).
Proof. exact (eq_refl (term645 _106189 _106193 K s k x i y)). Qed.
Lemma lem4412033 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type875 _106189 _106193 K) (x : type1518 _106189 _106193 K) (y : type1518 _106189 _106193 K) : (term644 _106189 _106193 K s k x i y) = (term646 _106189 _106193 K s k i x y).
Proof. exact (TRANS (@lem4412031 _106189 _106193 K s k x i y) (@lem4412032 _106189 _106193 K s k i x y)). Qed.
Lemma lem4412034 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type875 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (term647 _106189 _106193 K s k x i) = (term648 _106189 _106193 K s k i x).
Proof. exact (fun_ext (fun y : type1518 _106189 _106193 K => @lem4412033 _106189 _106193 K s k i x y)). Qed.
Lemma lem4412035 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4412036 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type875 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (term649 _106189 _106193 K s k x i) = (term650 _106189 _106193 K s k i x).
Proof. exact (MK_COMB (@lem4412035 _106189 _106193 K) (@lem4412034 _106189 _106193 K s k i x)). Qed.
Lemma lem4412037 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term651 _106189 _106193 K s k x) = (term652 _106189 _106193 K s k x).
Proof. exact (fun_ext (fun i : type875 _106189 _106193 K => @lem4412036 _106189 _106193 K s k i x)). Qed.
Lemma lem4412038 {_106189 _106193 K : Type'} : (@ex ((K -> _106193 -> _106189) -> K)) = (@ex ((K -> _106193 -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106193 -> _106189) -> K))). Qed.
Lemma lem4412039 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term634 _106189 _106193 K s k x) = (term653 _106189 _106193 K s k x).
Proof. exact (MK_COMB (@lem4412038 _106189 _106193 K) (@lem4412037 _106189 _106193 K s k x)). Qed.
Lemma lem4412040 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : ((term633 _106189 _106193 K s k x) = (term634 _106189 _106193 K s k x)) = ((term630 _106189 _106193 K s k x) = (term653 _106189 _106193 K s k x)).
Proof. exact (MK_COMB (@lem4412028 _106189 _106193 K s k x) (@lem4412039 _106189 _106193 K s k x)). Qed.
Lemma lem4412041 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term630 _106189 _106193 K s k x) = (term653 _106189 _106193 K s k x).
Proof. exact (EQ_MP (@lem4412040 _106189 _106193 K s k x) (@lem4412015 _106189 _106193 K s k x)). Qed.
Lemma lem4412042 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term579 _106189 _106193 K s k x) = (term653 _106189 _106193 K s k x).
Proof. exact (TRANS (@lem4412011 _106189 _106193 K s k x) (@lem4412041 _106189 _106193 K s k x)). Qed.
Lemma lem4412043 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term580 _106189 _106193 K s k) = (term654 _106189 _106193 K s k).
Proof. exact (fun_ext (fun x : type1518 _106189 _106193 K => @lem4412042 _106189 _106193 K s k x)). Qed.
Lemma lem4412044 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4412045 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term581 _106189 _106193 K s k) = (term655 _106189 _106193 K s k).
Proof. exact (MK_COMB (@lem4412044 _106189 _106193 K) (@lem4412043 _106189 _106193 K s k)). Qed.
Lemma lem4412047 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412048 {_106189 _106193 K : Type'} (P : type872 _106189 _106193 K) : (term656 _106189 _106193 K P) = (term657 _106189 _106193 K P).
Proof. exact (@lem4412047 (type1518 _106189 _106193 K) (type875 _106189 _106193 K) P). Qed.
Lemma lem4412049 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term658 _106189 _106193 K s k) = (term659 _106189 _106193 K s k).
Proof. exact (@lem4412048 _106189 _106193 K (term660 _106189 _106193 K s k)). Qed.
Lemma lem4412050 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term661 _106189 _106193 K s k x) = (term652 _106189 _106193 K s k x).
Proof. exact (eq_refl (term661 _106189 _106193 K s k x)). Qed.
Lemma lem4412051 {_106189 _106193 K : Type'} (i : type875 _106189 _106193 K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412052 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) (i : type875 _106189 _106193 K) : (term662 _106189 _106193 K s k x i) = (term663 _106189 _106193 K s k x i).
Proof. exact (MK_COMB (@lem4412050 _106189 _106193 K s k x) (@lem4412051 _106189 _106193 K i)). Qed.
Lemma lem4412053 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type875 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (term663 _106189 _106193 K s k x i) = (term650 _106189 _106193 K s k i x).
Proof. exact (eq_refl (term663 _106189 _106193 K s k x i)). Qed.
Lemma lem4412054 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type875 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (term662 _106189 _106193 K s k x i) = (term650 _106189 _106193 K s k i x).
Proof. exact (TRANS (@lem4412052 _106189 _106193 K s k x i) (@lem4412053 _106189 _106193 K s k i x)). Qed.
Lemma lem4412055 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term664 _106189 _106193 K s k x) = (term652 _106189 _106193 K s k x).
Proof. exact (fun_ext (fun i : type875 _106189 _106193 K => @lem4412054 _106189 _106193 K s k i x)). Qed.
Lemma lem4412056 {_106189 _106193 K : Type'} : (@ex ((K -> _106193 -> _106189) -> K)) = (@ex ((K -> _106193 -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106193 -> _106189) -> K))). Qed.
Lemma lem4412057 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term665 _106189 _106193 K s k x) = (term653 _106189 _106193 K s k x).
Proof. exact (MK_COMB (@lem4412056 _106189 _106193 K) (@lem4412055 _106189 _106193 K s k x)). Qed.
Lemma lem4412058 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term666 _106189 _106193 K s k) = (term654 _106189 _106193 K s k).
Proof. exact (fun_ext (fun x : type1518 _106189 _106193 K => @lem4412057 _106189 _106193 K s k x)). Qed.
Lemma lem4412059 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4412060 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term658 _106189 _106193 K s k) = (term655 _106189 _106193 K s k).
Proof. exact (MK_COMB (@lem4412059 _106189 _106193 K) (@lem4412058 _106189 _106193 K s k)). Qed.
Lemma lem4412061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412062 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term667 _106189 _106193 K s k) = (term668 _106189 _106193 K s k).
Proof. exact (MK_COMB (@lem4412061) (@lem4412060 _106189 _106193 K s k)). Qed.
Lemma lem4412063 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (x : type1518 _106189 _106193 K) : (term661 _106189 _106193 K s k x) = (term652 _106189 _106193 K s k x).
Proof. exact (eq_refl (term661 _106189 _106193 K s k x)). Qed.
Lemma lem4412064 {_106189 _106193 K : Type'} (i : type873 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem4412065 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (term669 _106189 _106193 K s k i x) = (term670 _106189 _106193 K s k i x).
Proof. exact (MK_COMB (@lem4412063 _106189 _106193 K s k x) (@lem4412064 _106189 _106193 K i x)). Qed.
Lemma lem4412066 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (term670 _106189 _106193 K s k i x) = (term671 _106189 _106193 K s k i x).
Proof. exact (eq_refl (term670 _106189 _106193 K s k i x)). Qed.
Lemma lem4412067 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) (x : type1518 _106189 _106193 K) : (term669 _106189 _106193 K s k i x) = (term671 _106189 _106193 K s k i x).
Proof. exact (TRANS (@lem4412065 _106189 _106193 K s k i x) (@lem4412066 _106189 _106193 K s k i x)). Qed.
Lemma lem4412068 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) : (term672 _106189 _106193 K s k i) = (term673 _106189 _106193 K s k i).
Proof. exact (fun_ext (fun x : type1518 _106189 _106193 K => @lem4412067 _106189 _106193 K s k i x)). Qed.
Lemma lem4412069 {_106189 _106193 K : Type'} : (@all (K -> _106193 -> _106189)) = (@all (K -> _106193 -> _106189)).
Proof. exact (eq_refl (@all (K -> _106193 -> _106189))). Qed.
Lemma lem4412070 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) : (term674 _106189 _106193 K s k i) = (term675 _106189 _106193 K s k i).
Proof. exact (MK_COMB (@lem4412069 _106189 _106193 K) (@lem4412068 _106189 _106193 K s k i)). Qed.
Lemma lem4412071 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term676 _106189 _106193 K s k) = (term677 _106189 _106193 K s k).
Proof. exact (fun_ext (fun i : type873 _106189 _106193 K => @lem4412070 _106189 _106193 K s k i)). Qed.
Lemma lem4412072 {_106189 _106193 K : Type'} : (@ex ((K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)) = (@ex ((K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K))). Qed.
Lemma lem4412073 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term659 _106189 _106193 K s k) = (term678 _106189 _106193 K s k).
Proof. exact (MK_COMB (@lem4412072 _106189 _106193 K) (@lem4412071 _106189 _106193 K s k)). Qed.
Lemma lem4412074 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : ((term658 _106189 _106193 K s k) = (term659 _106189 _106193 K s k)) = ((term655 _106189 _106193 K s k) = (term678 _106189 _106193 K s k)).
Proof. exact (MK_COMB (@lem4412062 _106189 _106193 K s k) (@lem4412073 _106189 _106193 K s k)). Qed.
Lemma lem4412075 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term655 _106189 _106193 K s k) = (term678 _106189 _106193 K s k).
Proof. exact (EQ_MP (@lem4412074 _106189 _106193 K s k) (@lem4412049 _106189 _106193 K s k)). Qed.
Lemma lem4412076 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term581 _106189 _106193 K s k) = (term678 _106189 _106193 K s k).
Proof. exact (TRANS (@lem4412045 _106189 _106193 K s k) (@lem4412075 _106189 _106193 K s k)). Qed.
Lemma lem4412077 {_106189 _106193 K : Type'} (k : K -> Prop) : (term582 _106189 _106193 K k) = (term679 _106189 _106193 K k).
Proof. exact (fun_ext (fun s : type1508 _106189 _106193 K => @lem4412076 _106189 _106193 K s k)). Qed.
Lemma lem4412078 {_106189 _106193 K : Type'} : (@all (K -> (_106193 -> _106189) -> Prop)) = (@all (K -> (_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all (K -> (_106193 -> _106189) -> Prop))). Qed.
Lemma lem4412079 {_106189 _106193 K : Type'} (k : K -> Prop) : (term583 _106189 _106193 K k) = (term680 _106189 _106193 K k).
Proof. exact (MK_COMB (@lem4412078 _106189 _106193 K) (@lem4412077 _106189 _106193 K k)). Qed.
Lemma lem4412081 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412082 {_106189 _106193 K : Type'} (P : type865 _106189 _106193 K) : (term681 _106189 _106193 K P) = (term682 _106189 _106193 K P).
Proof. exact (@lem4412081 (type1508 _106189 _106193 K) (type873 _106189 _106193 K) P). Qed.
Lemma lem4412083 {_106189 _106193 K : Type'} (k : K -> Prop) : (term683 _106189 _106193 K k) = (term684 _106189 _106193 K k).
Proof. exact (@lem4412082 _106189 _106193 K (term685 _106189 _106193 K k)). Qed.
Lemma lem4412084 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term686 _106189 _106193 K k s) = (term677 _106189 _106193 K s k).
Proof. exact (eq_refl (term686 _106189 _106193 K k s)). Qed.
Lemma lem4412085 {_106189 _106193 K : Type'} (i : type873 _106189 _106193 K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412086 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) : (term687 _106189 _106193 K k s i) = (term688 _106189 _106193 K s k i).
Proof. exact (MK_COMB (@lem4412084 _106189 _106193 K s k) (@lem4412085 _106189 _106193 K i)). Qed.
Lemma lem4412087 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) : (term688 _106189 _106193 K s k i) = (term675 _106189 _106193 K s k i).
Proof. exact (eq_refl (term688 _106189 _106193 K s k i)). Qed.
Lemma lem4412088 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) (i : type873 _106189 _106193 K) : (term687 _106189 _106193 K k s i) = (term675 _106189 _106193 K s k i).
Proof. exact (TRANS (@lem4412086 _106189 _106193 K s k i) (@lem4412087 _106189 _106193 K s k i)). Qed.
Lemma lem4412089 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term689 _106189 _106193 K k s) = (term677 _106189 _106193 K s k).
Proof. exact (fun_ext (fun i : type873 _106189 _106193 K => @lem4412088 _106189 _106193 K s k i)). Qed.
Lemma lem4412090 {_106189 _106193 K : Type'} : (@ex ((K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)) = (@ex ((K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K))). Qed.
Lemma lem4412091 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term690 _106189 _106193 K k s) = (term678 _106189 _106193 K s k).
Proof. exact (MK_COMB (@lem4412090 _106189 _106193 K) (@lem4412089 _106189 _106193 K s k)). Qed.
Lemma lem4412092 {_106189 _106193 K : Type'} (k : K -> Prop) : (term691 _106189 _106193 K k) = (term679 _106189 _106193 K k).
Proof. exact (fun_ext (fun s : type1508 _106189 _106193 K => @lem4412091 _106189 _106193 K s k)). Qed.
Lemma lem4412093 {_106189 _106193 K : Type'} : (@all (K -> (_106193 -> _106189) -> Prop)) = (@all (K -> (_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all (K -> (_106193 -> _106189) -> Prop))). Qed.
Lemma lem4412094 {_106189 _106193 K : Type'} (k : K -> Prop) : (term683 _106189 _106193 K k) = (term680 _106189 _106193 K k).
Proof. exact (MK_COMB (@lem4412093 _106189 _106193 K) (@lem4412092 _106189 _106193 K k)). Qed.
Lemma lem4412095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412096 {_106189 _106193 K : Type'} (k : K -> Prop) : (term692 _106189 _106193 K k) = (term693 _106189 _106193 K k).
Proof. exact (MK_COMB (@lem4412095) (@lem4412094 _106189 _106193 K k)). Qed.
Lemma lem4412097 {_106189 _106193 K : Type'} (s : type1508 _106189 _106193 K) (k : K -> Prop) : (term686 _106189 _106193 K k s) = (term677 _106189 _106193 K s k).
Proof. exact (eq_refl (term686 _106189 _106193 K k s)). Qed.
Lemma lem4412098 {_106189 _106193 K : Type'} (i : type866 _106189 _106193 K) (s : type1508 _106189 _106193 K) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem4412099 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) (s : type1508 _106189 _106193 K) : (term694 _106189 _106193 K k i s) = (term695 _106189 _106193 K k i s).
Proof. exact (MK_COMB (@lem4412097 _106189 _106193 K s k) (@lem4412098 _106189 _106193 K i s)). Qed.
Lemma lem4412100 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) (s : type1508 _106189 _106193 K) : (term695 _106189 _106193 K k i s) = (term696 _106189 _106193 K k i s).
Proof. exact (eq_refl (term695 _106189 _106193 K k i s)). Qed.
Lemma lem4412101 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) (s : type1508 _106189 _106193 K) : (term694 _106189 _106193 K k i s) = (term696 _106189 _106193 K k i s).
Proof. exact (TRANS (@lem4412099 _106189 _106193 K k i s) (@lem4412100 _106189 _106193 K k i s)). Qed.
Lemma lem4412102 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) : (term697 _106189 _106193 K k i) = (term698 _106189 _106193 K k i).
Proof. exact (fun_ext (fun s : type1508 _106189 _106193 K => @lem4412101 _106189 _106193 K k i s)). Qed.
Lemma lem4412103 {_106189 _106193 K : Type'} : (@all (K -> (_106193 -> _106189) -> Prop)) = (@all (K -> (_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all (K -> (_106193 -> _106189) -> Prop))). Qed.
Lemma lem4412104 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) : (term699 _106189 _106193 K k i) = (term700 _106189 _106193 K k i).
Proof. exact (MK_COMB (@lem4412103 _106189 _106193 K) (@lem4412102 _106189 _106193 K k i)). Qed.
Lemma lem4412105 {_106189 _106193 K : Type'} (k : K -> Prop) : (term701 _106189 _106193 K k) = (term702 _106189 _106193 K k).
Proof. exact (fun_ext (fun i : type866 _106189 _106193 K => @lem4412104 _106189 _106193 K k i)). Qed.
Lemma lem4412106 {_106189 _106193 K : Type'} : (@ex ((K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)) = (@ex ((K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K))). Qed.
Lemma lem4412107 {_106189 _106193 K : Type'} (k : K -> Prop) : (term684 _106189 _106193 K k) = (term703 _106189 _106193 K k).
Proof. exact (MK_COMB (@lem4412106 _106189 _106193 K) (@lem4412105 _106189 _106193 K k)). Qed.
Lemma lem4412108 {_106189 _106193 K : Type'} (k : K -> Prop) : ((term683 _106189 _106193 K k) = (term684 _106189 _106193 K k)) = ((term680 _106189 _106193 K k) = (term703 _106189 _106193 K k)).
Proof. exact (MK_COMB (@lem4412096 _106189 _106193 K k) (@lem4412107 _106189 _106193 K k)). Qed.
Lemma lem4412109 {_106189 _106193 K : Type'} (k : K -> Prop) : (term680 _106189 _106193 K k) = (term703 _106189 _106193 K k).
Proof. exact (EQ_MP (@lem4412108 _106189 _106193 K k) (@lem4412083 _106189 _106193 K k)). Qed.
Lemma lem4412110 {_106189 _106193 K : Type'} (k : K -> Prop) : (term583 _106189 _106193 K k) = (term703 _106189 _106193 K k).
Proof. exact (TRANS (@lem4412079 _106189 _106193 K k) (@lem4412109 _106189 _106193 K k)). Qed.
Lemma lem4412111 {_106189 _106193 K : Type'} : (term584 _106189 _106193 K) = (term704 _106189 _106193 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4412110 _106189 _106193 K k)). Qed.
Lemma lem4412112 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4412113 {_106189 _106193 K : Type'} : (term585 _106189 _106193 K) = (term705 _106189 _106193 K).
Proof. exact (MK_COMB (@lem4412112 K) (@lem4412111 _106189 _106193 K)). Qed.
Lemma lem4412115 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412116 {_106189 _106193 K : Type'} (P : type890 _106189 _106193 K) : (term706 _106189 _106193 K P) = (term707 _106189 _106193 K P).
Proof. exact (@lem4412115 (K -> Prop) (type866 _106189 _106193 K) P). Qed.
Lemma lem4412117 {_106189 _106193 K : Type'} : (term708 _106189 _106193 K) = (term709 _106189 _106193 K).
Proof. exact (@lem4412116 _106189 _106193 K (term710 _106189 _106193 K)). Qed.
Lemma lem4412118 {_106189 _106193 K : Type'} (k : K -> Prop) : (term711 _106189 _106193 K k) = (term702 _106189 _106193 K k).
Proof. exact (eq_refl (term711 _106189 _106193 K k)). Qed.
Lemma lem4412119 {_106189 _106193 K : Type'} (i : type866 _106189 _106193 K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412120 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) : (term712 _106189 _106193 K k i) = (term713 _106189 _106193 K k i).
Proof. exact (MK_COMB (@lem4412118 _106189 _106193 K k) (@lem4412119 _106189 _106193 K i)). Qed.
Lemma lem4412121 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) : (term713 _106189 _106193 K k i) = (term700 _106189 _106193 K k i).
Proof. exact (eq_refl (term713 _106189 _106193 K k i)). Qed.
Lemma lem4412122 {_106189 _106193 K : Type'} (k : K -> Prop) (i : type866 _106189 _106193 K) : (term712 _106189 _106193 K k i) = (term700 _106189 _106193 K k i).
Proof. exact (TRANS (@lem4412120 _106189 _106193 K k i) (@lem4412121 _106189 _106193 K k i)). Qed.
Lemma lem4412123 {_106189 _106193 K : Type'} (k : K -> Prop) : (term714 _106189 _106193 K k) = (term702 _106189 _106193 K k).
Proof. exact (fun_ext (fun i : type866 _106189 _106193 K => @lem4412122 _106189 _106193 K k i)). Qed.
Lemma lem4412124 {_106189 _106193 K : Type'} : (@ex ((K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)) = (@ex ((K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K))). Qed.
Lemma lem4412125 {_106189 _106193 K : Type'} (k : K -> Prop) : (term715 _106189 _106193 K k) = (term703 _106189 _106193 K k).
Proof. exact (MK_COMB (@lem4412124 _106189 _106193 K) (@lem4412123 _106189 _106193 K k)). Qed.
Lemma lem4412126 {_106189 _106193 K : Type'} : (term716 _106189 _106193 K) = (term704 _106189 _106193 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4412125 _106189 _106193 K k)). Qed.
Lemma lem4412127 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4412128 {_106189 _106193 K : Type'} : (term708 _106189 _106193 K) = (term705 _106189 _106193 K).
Proof. exact (MK_COMB (@lem4412127 K) (@lem4412126 _106189 _106193 K)). Qed.
Lemma lem4412129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412130 {_106189 _106193 K : Type'} : (term717 _106189 _106193 K) = (term718 _106189 _106193 K).
Proof. exact (MK_COMB (@lem4412129) (@lem4412128 _106189 _106193 K)). Qed.
Lemma lem4412131 {_106189 _106193 K : Type'} (k : K -> Prop) : (term711 _106189 _106193 K k) = (term702 _106189 _106193 K k).
Proof. exact (eq_refl (term711 _106189 _106193 K k)). Qed.
Lemma lem4412132 {_106189 _106193 K : Type'} (i : type891 _106189 _106193 K) (k : K -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem4412133 {_106189 _106193 K : Type'} (i : type891 _106189 _106193 K) (k : K -> Prop) : (term719 _106189 _106193 K i k) = (term720 _106189 _106193 K i k).
Proof. exact (MK_COMB (@lem4412131 _106189 _106193 K k) (@lem4412132 _106189 _106193 K i k)). Qed.
Lemma lem4412134 {_106189 _106193 K : Type'} (i : type891 _106189 _106193 K) (k : K -> Prop) : (term720 _106189 _106193 K i k) = (term721 _106189 _106193 K i k).
Proof. exact (eq_refl (term720 _106189 _106193 K i k)). Qed.
Lemma lem4412135 {_106189 _106193 K : Type'} (i : type891 _106189 _106193 K) (k : K -> Prop) : (term719 _106189 _106193 K i k) = (term721 _106189 _106193 K i k).
Proof. exact (TRANS (@lem4412133 _106189 _106193 K i k) (@lem4412134 _106189 _106193 K i k)). Qed.
Lemma lem4412136 {_106189 _106193 K : Type'} (i : type891 _106189 _106193 K) : (term722 _106189 _106193 K i) = (term723 _106189 _106193 K i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4412135 _106189 _106193 K i k)). Qed.
Lemma lem4412137 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4412138 {_106189 _106193 K : Type'} (i : type891 _106189 _106193 K) : (term724 _106189 _106193 K i) = (term725 _106189 _106193 K i).
Proof. exact (MK_COMB (@lem4412137 K) (@lem4412136 _106189 _106193 K i)). Qed.
Lemma lem4412139 {_106189 _106193 K : Type'} : (term726 _106189 _106193 K) = (term727 _106189 _106193 K).
Proof. exact (fun_ext (fun i : type891 _106189 _106193 K => @lem4412138 _106189 _106193 K i)). Qed.
Lemma lem4412140 {_106189 _106193 K : Type'} : (@ex ((K -> Prop) -> (K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)) = (@ex ((K -> Prop) -> (K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> (_106193 -> _106189) -> Prop) -> (K -> _106193 -> _106189) -> (K -> _106193 -> _106189) -> K))). Qed.
Lemma lem4412141 {_106189 _106193 K : Type'} : (term709 _106189 _106193 K) = (term728 _106189 _106193 K).
Proof. exact (MK_COMB (@lem4412140 _106189 _106193 K) (@lem4412139 _106189 _106193 K)). Qed.
Lemma lem4412142 {_106189 _106193 K : Type'} : ((term708 _106189 _106193 K) = (term709 _106189 _106193 K)) = ((term705 _106189 _106193 K) = (term728 _106189 _106193 K)).
Proof. exact (MK_COMB (@lem4412130 _106189 _106193 K) (@lem4412141 _106189 _106193 K)). Qed.
Lemma lem4412143 {_106189 _106193 K : Type'} : (term705 _106189 _106193 K) = (term728 _106189 _106193 K).
Proof. exact (EQ_MP (@lem4412142 _106189 _106193 K) (@lem4412117 _106189 _106193 K)). Qed.
Lemma lem4412145 {_106189 _106193 K : Type'} : (term585 _106189 _106193 K) = (term728 _106189 _106193 K).
Proof. exact (TRANS (@lem4412113 _106189 _106193 K) (@lem4412143 _106189 _106193 K)). Qed.
Lemma lem4412146 {_106189 _106193 K : Type'} : (term14 _106189 _106193 K) = (term728 _106189 _106193 K).
Proof. exact (TRANS (@lem4411827 _106189 _106193 K) (@lem4412145 _106189 _106193 K)). Qed.
Lemma lem4412147 {_106189 _106193 K : Type'} (h1 : term14 _106189 _106193 K) : term728 _106189 _106193 K.
Proof. exact (EQ_MP (@lem4412146 _106189 _106193 K) (@lem4410344 _106189 _106193 K h1)). Qed.
Lemma lem4412156 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term729 _106189 _106193 A k x y i) = (term730 _106189 _106193 A k x y i).
Proof. exact (@lem17362 (@IN (_106193 -> _106189) i k) ((x i) = (y i))). Qed.
Lemma lem4412157 {_106189 _106193 : Type'} (P : type805 _106189 _106193) : (term134 _106189 _106193 P) = (term135 _106189 _106193 P).
Proof. exact (@lem18392 (_106193 -> _106189) P). Qed.
Lemma lem4412158 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term731 _106189 _106193 A k x y) = (term732 _106189 _106193 A k x y).
Proof. exact (@lem4412157 _106189 _106193 (term35 _106189 _106193 A k x y)). Qed.
Lemma lem4412159 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term733 _106189 _106193 A k x y i) = (term34 _106189 _106193 A k x y i).
Proof. exact (eq_refl (term733 _106189 _106193 A k x y i)). Qed.
Lemma lem4412160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4412161 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term734 _106189 _106193 A k x y i) = (term729 _106189 _106193 A k x y i).
Proof. exact (MK_COMB (@lem4412160) (@lem4412159 _106189 _106193 A k x y i)). Qed.
Lemma lem4412162 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term734 _106189 _106193 A k x y i) = (term730 _106189 _106193 A k x y i).
Proof. exact (TRANS (@lem4412161 _106189 _106193 A k x y i) (@lem4412156 _106189 _106193 A k x y i)). Qed.
Lemma lem4412163 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term735 _106189 _106193 A k x y) = (term736 _106189 _106193 A k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412162 _106189 _106193 A k x y i)). Qed.
Lemma lem4412164 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412165 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term732 _106189 _106193 A k x y) = (term737 _106189 _106193 A k x y).
Proof. exact (MK_COMB (@lem4412164 _106189 _106193) (@lem4412163 _106189 _106193 A k x y)). Qed.
Lemma lem4412166 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term731 _106189 _106193 A k x y) = (term737 _106189 _106193 A k x y).
Proof. exact (TRANS (@lem4412158 _106189 _106193 A k x y) (@lem4412165 _106189 _106193 A k x y)). Qed.
Lemma lem4412168 {_106189 _106193 A : Type'} (y : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term738 _106189 _106193 A y k s) = (term738 _106189 _106193 A y k s).
Proof. exact (eq_refl (term738 _106189 _106193 A y k s)). Qed.
Lemma lem4412169 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term739 _106189 _106193 A s k x y) = (term740 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412168 _106189 _106193 A y k s) (@lem4412166 _106189 _106193 A k x y)). Qed.
Lemma lem4412170 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term741 _106189 _106193 A s k x y) = (term739 _106189 _106193 A s k x y).
Proof. exact (@lem17045 (term742 _106189 _106193 A y k s) (term36 _106189 _106193 A k x y)). Qed.
Lemma lem4412171 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term741 _106189 _106193 A s k x y) = (term740 _106189 _106193 A s k x y).
Proof. exact (TRANS (@lem4412170 _106189 _106193 A s k x y) (@lem4412169 _106189 _106193 A s k x y)). Qed.
Lemma lem4412173 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term738 _106189 _106193 A x k s) = (term738 _106189 _106193 A x k s).
Proof. exact (eq_refl (term738 _106189 _106193 A x k s)). Qed.
Lemma lem4412174 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term743 _106189 _106193 A s k x y) = (term744 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412173 _106189 _106193 A x k s) (@lem4412171 _106189 _106193 A s k x y)). Qed.
Lemma lem4412175 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term745 _106189 _106193 A s k x y) = (term743 _106189 _106193 A s k x y).
Proof. exact (@lem17045 (term742 _106189 _106193 A x k s) (term38 _106189 _106193 A s k x y)). Qed.
Lemma lem4412176 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term745 _106189 _106193 A s k x y) = (term744 _106189 _106193 A s k x y).
Proof. exact (TRANS (@lem4412175 _106189 _106193 A s k x y) (@lem4412174 _106189 _106193 A s k x y)). Qed.
Lemma lem4412177 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4412178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4412179 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term746 _106189 _106193 A s k x y) = (term747 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412178) (@lem4412176 _106189 _106193 A s k x y)). Qed.
Lemma lem4412180 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term748 _106189 _106193 A s k x y) = (term749 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412179 _106189 _106193 A s k x y) (@lem4412177 _106189 _106193 A x y)). Qed.
Lemma lem4412181 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term41 _106189 _106193 A s k x y) = (term748 _106189 _106193 A s k x y).
Proof. exact (@lem17265 (term39 _106189 _106193 A s k x y) (x = y)). Qed.
Lemma lem4412182 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term41 _106189 _106193 A s k x y) = (term749 _106189 _106193 A s k x y).
Proof. exact (TRANS (@lem4412181 _106189 _106193 A s k x y) (@lem4412180 _106189 _106193 A s k x y)). Qed.
Lemma lem4412183 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term42 _106189 _106193 A s k x) = (term750 _106189 _106193 A s k x).
Proof. exact (fun_ext (fun y : type804 _106189 _106193 A => @lem4412182 _106189 _106193 A s k x y)). Qed.
Lemma lem4412184 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412185 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term43 _106189 _106193 A s k x) = (term751 _106189 _106193 A s k x).
Proof. exact (MK_COMB (@lem4412184 _106189 _106193 A) (@lem4412183 _106189 _106193 A s k x)). Qed.
Lemma lem4412186 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term44 _106189 _106193 A s k) = (term752 _106189 _106193 A s k).
Proof. exact (fun_ext (fun x : type804 _106189 _106193 A => @lem4412185 _106189 _106193 A s k x)). Qed.
Lemma lem4412187 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412188 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term45 _106189 _106193 A s k) = (term753 _106189 _106193 A s k).
Proof. exact (MK_COMB (@lem4412187 _106189 _106193 A) (@lem4412186 _106189 _106193 A s k)). Qed.
Lemma lem4412189 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term46 _106189 _106193 A k) = (term754 _106189 _106193 A k).
Proof. exact (fun_ext (fun s : type800 _106189 _106193 A => @lem4412188 _106189 _106193 A s k)). Qed.
Lemma lem4412190 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A -> Prop)) = (@all ((_106193 -> _106189) -> A -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A -> Prop))). Qed.
Lemma lem4412191 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term47 _106189 _106193 A k) = (term755 _106189 _106193 A k).
Proof. exact (MK_COMB (@lem4412190 _106189 _106193 A) (@lem4412189 _106189 _106193 A k)). Qed.
Lemma lem4412192 {_106189 _106193 A : Type'} : (term48 _106189 _106193 A) = (term756 _106189 _106193 A).
Proof. exact (fun_ext (fun k : type805 _106189 _106193 => @lem4412191 _106189 _106193 A k)). Qed.
Lemma lem4412193 {_106189 _106193 : Type'} : (@all ((_106193 -> _106189) -> Prop)) = (@all ((_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> Prop))). Qed.
Lemma lem4412194 {_106189 _106193 A : Type'} : (term12 _106189 _106193 A) = (term757 _106189 _106193 A).
Proof. exact (MK_COMB (@lem4412193 _106189 _106193) (@lem4412192 _106189 _106193 A)). Qed.
Lemma lem4412305 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4412306 {_106189 _106193 : Type'} (P : Prop) (Q : type805 _106189 _106193) : (term758 _106189 _106193 P Q) = (term759 _106189 _106193 P Q).
Proof. exact (@lem4412305 (_106193 -> _106189) P Q). Qed.
Lemma lem4412307 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term760 _106189 _106193 A s k x y) = (term761 _106189 _106193 A s k x y).
Proof. exact (@lem4412306 _106189 _106193 (term762 _106189 _106193 A y k s) (term736 _106189 _106193 A k x y)). Qed.
Lemma lem4412308 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term763 _106189 _106193 A k x y i) = (term730 _106189 _106193 A k x y i).
Proof. exact (eq_refl (term763 _106189 _106193 A k x y i)). Qed.
Lemma lem4412309 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term764 _106189 _106193 A k x y) = (term736 _106189 _106193 A k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412308 _106189 _106193 A k x y i)). Qed.
Lemma lem4412310 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412311 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term765 _106189 _106193 A k x y) = (term737 _106189 _106193 A k x y).
Proof. exact (MK_COMB (@lem4412310 _106189 _106193) (@lem4412309 _106189 _106193 A k x y)). Qed.
Lemma lem4412312 {_106189 _106193 A : Type'} (y : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term738 _106189 _106193 A y k s) = (term738 _106189 _106193 A y k s).
Proof. exact (eq_refl (term738 _106189 _106193 A y k s)). Qed.
Lemma lem4412313 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term760 _106189 _106193 A s k x y) = (term740 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412312 _106189 _106193 A y k s) (@lem4412311 _106189 _106193 A k x y)). Qed.
Lemma lem4412314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412315 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term766 _106189 _106193 A s k x y) = (term767 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412314) (@lem4412313 _106189 _106193 A s k x y)). Qed.
Lemma lem4412316 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term763 _106189 _106193 A k x y i) = (term730 _106189 _106193 A k x y i).
Proof. exact (eq_refl (term763 _106189 _106193 A k x y i)). Qed.
Lemma lem4412317 {_106189 _106193 A : Type'} (y : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term738 _106189 _106193 A y k s) = (term738 _106189 _106193 A y k s).
Proof. exact (eq_refl (term738 _106189 _106193 A y k s)). Qed.
Lemma lem4412318 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term768 _106189 _106193 A s k x y i) = (term769 _106189 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4412317 _106189 _106193 A y k s) (@lem4412316 _106189 _106193 A k x y i)). Qed.
Lemma lem4412319 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term770 _106189 _106193 A s k x y) = (term771 _106189 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412318 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412320 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412321 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term761 _106189 _106193 A s k x y) = (term772 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412320 _106189 _106193) (@lem4412319 _106189 _106193 A s k x y)). Qed.
Lemma lem4412322 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : ((term760 _106189 _106193 A s k x y) = (term761 _106189 _106193 A s k x y)) = ((term740 _106189 _106193 A s k x y) = (term772 _106189 _106193 A s k x y)).
Proof. exact (MK_COMB (@lem4412315 _106189 _106193 A s k x y) (@lem4412321 _106189 _106193 A s k x y)). Qed.
Lemma lem4412323 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term740 _106189 _106193 A s k x y) = (term772 _106189 _106193 A s k x y).
Proof. exact (EQ_MP (@lem4412322 _106189 _106193 A s k x y) (@lem4412307 _106189 _106193 A s k x y)). Qed.
Lemma lem4412324 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term738 _106189 _106193 A x k s) = (term738 _106189 _106193 A x k s).
Proof. exact (eq_refl (term738 _106189 _106193 A x k s)). Qed.
Lemma lem4412325 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term744 _106189 _106193 A s k x y) = (term773 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412324 _106189 _106193 A x k s) (@lem4412323 _106189 _106193 A s k x y)). Qed.
Lemma lem4412327 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4412328 {_106189 _106193 : Type'} (P : Prop) (Q : type805 _106189 _106193) : (term758 _106189 _106193 P Q) = (term759 _106189 _106193 P Q).
Proof. exact (@lem4412327 (_106193 -> _106189) P Q). Qed.
Lemma lem4412329 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term774 _106189 _106193 A s k x y) = (term775 _106189 _106193 A s k x y).
Proof. exact (@lem4412328 _106189 _106193 (term762 _106189 _106193 A x k s) (term771 _106189 _106193 A s k x y)). Qed.
Lemma lem4412330 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term776 _106189 _106193 A s k x y i) = (term769 _106189 _106193 A s k x y i).
Proof. exact (eq_refl (term776 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412331 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term777 _106189 _106193 A s k x y) = (term771 _106189 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412330 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412332 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412333 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term778 _106189 _106193 A s k x y) = (term772 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412332 _106189 _106193) (@lem4412331 _106189 _106193 A s k x y)). Qed.
Lemma lem4412334 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term738 _106189 _106193 A x k s) = (term738 _106189 _106193 A x k s).
Proof. exact (eq_refl (term738 _106189 _106193 A x k s)). Qed.
Lemma lem4412335 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term774 _106189 _106193 A s k x y) = (term773 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412334 _106189 _106193 A x k s) (@lem4412333 _106189 _106193 A s k x y)). Qed.
Lemma lem4412336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412337 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term779 _106189 _106193 A s k x y) = (term780 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412336) (@lem4412335 _106189 _106193 A s k x y)). Qed.
Lemma lem4412338 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term776 _106189 _106193 A s k x y i) = (term769 _106189 _106193 A s k x y i).
Proof. exact (eq_refl (term776 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412339 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (k : type805 _106189 _106193) (s : type800 _106189 _106193 A) : (term738 _106189 _106193 A x k s) = (term738 _106189 _106193 A x k s).
Proof. exact (eq_refl (term738 _106189 _106193 A x k s)). Qed.
Lemma lem4412340 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term781 _106189 _106193 A s k x y i) = (term782 _106189 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4412339 _106189 _106193 A x k s) (@lem4412338 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412341 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term783 _106189 _106193 A s k x y) = (term784 _106189 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412340 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412342 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412343 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term775 _106189 _106193 A s k x y) = (term785 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412342 _106189 _106193) (@lem4412341 _106189 _106193 A s k x y)). Qed.
Lemma lem4412344 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : ((term774 _106189 _106193 A s k x y) = (term775 _106189 _106193 A s k x y)) = ((term773 _106189 _106193 A s k x y) = (term785 _106189 _106193 A s k x y)).
Proof. exact (MK_COMB (@lem4412337 _106189 _106193 A s k x y) (@lem4412343 _106189 _106193 A s k x y)). Qed.
Lemma lem4412345 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term773 _106189 _106193 A s k x y) = (term785 _106189 _106193 A s k x y).
Proof. exact (EQ_MP (@lem4412344 _106189 _106193 A s k x y) (@lem4412329 _106189 _106193 A s k x y)). Qed.
Lemma lem4412346 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term744 _106189 _106193 A s k x y) = (term785 _106189 _106193 A s k x y).
Proof. exact (TRANS (@lem4412325 _106189 _106193 A s k x y) (@lem4412345 _106189 _106193 A s k x y)). Qed.
Lemma lem4412347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4412348 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term747 _106189 _106193 A s k x y) = (term786 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412347) (@lem4412346 _106189 _106193 A s k x y)). Qed.
Lemma lem4412349 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4412350 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term749 _106189 _106193 A s k x y) = (term787 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412348 _106189 _106193 A s k x y) (@lem4412349 _106189 _106193 A x y)). Qed.
Lemma lem4412352 {A : Type'} (P : A -> Prop) (Q : Prop) : (term183 A P Q) = (term184 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4412353 {_106189 _106193 : Type'} (P : type805 _106189 _106193) (Q : Prop) : (term788 _106189 _106193 P Q) = (term789 _106189 _106193 P Q).
Proof. exact (@lem4412352 (_106193 -> _106189) P Q). Qed.
Lemma lem4412354 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term790 _106189 _106193 A s k x y) = (term791 _106189 _106193 A s k x y).
Proof. exact (@lem4412353 _106189 _106193 (term784 _106189 _106193 A s k x y) (x = y)). Qed.
Lemma lem4412355 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term792 _106189 _106193 A s k x y i) = (term782 _106189 _106193 A s k x y i).
Proof. exact (eq_refl (term792 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412356 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term793 _106189 _106193 A s k x y) = (term784 _106189 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412355 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412357 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412358 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term794 _106189 _106193 A s k x y) = (term785 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412357 _106189 _106193) (@lem4412356 _106189 _106193 A s k x y)). Qed.
Lemma lem4412359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4412360 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term795 _106189 _106193 A s k x y) = (term786 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412359) (@lem4412358 _106189 _106193 A s k x y)). Qed.
Lemma lem4412361 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4412362 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term790 _106189 _106193 A s k x y) = (term787 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412360 _106189 _106193 A s k x y) (@lem4412361 _106189 _106193 A x y)). Qed.
Lemma lem4412363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412364 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term796 _106189 _106193 A s k x y) = (term797 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412363) (@lem4412362 _106189 _106193 A s k x y)). Qed.
Lemma lem4412365 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term792 _106189 _106193 A s k x y i) = (term782 _106189 _106193 A s k x y i).
Proof. exact (eq_refl (term792 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4412367 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term798 _106189 _106193 A s k x y i) = (term799 _106189 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4412366) (@lem4412365 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412368 {_106189 _106193 A : Type'} (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4412369 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : _106193 -> _106189) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term800 _106189 _106193 A s k i x y) = (term801 _106189 _106193 A s k i x y).
Proof. exact (MK_COMB (@lem4412367 _106189 _106193 A s k x y i) (@lem4412368 _106189 _106193 A x y)). Qed.
Lemma lem4412370 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term802 _106189 _106193 A s k x y) = (term803 _106189 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412369 _106189 _106193 A s k i x y)). Qed.
Lemma lem4412371 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412372 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term791 _106189 _106193 A s k x y) = (term804 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412371 _106189 _106193) (@lem4412370 _106189 _106193 A s k x y)). Qed.
Lemma lem4412373 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : ((term790 _106189 _106193 A s k x y) = (term791 _106189 _106193 A s k x y)) = ((term787 _106189 _106193 A s k x y) = (term804 _106189 _106193 A s k x y)).
Proof. exact (MK_COMB (@lem4412364 _106189 _106193 A s k x y) (@lem4412372 _106189 _106193 A s k x y)). Qed.
Lemma lem4412374 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term787 _106189 _106193 A s k x y) = (term804 _106189 _106193 A s k x y).
Proof. exact (EQ_MP (@lem4412373 _106189 _106193 A s k x y) (@lem4412354 _106189 _106193 A s k x y)). Qed.
Lemma lem4412375 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term749 _106189 _106193 A s k x y) = (term804 _106189 _106193 A s k x y).
Proof. exact (TRANS (@lem4412350 _106189 _106193 A s k x y) (@lem4412374 _106189 _106193 A s k x y)). Qed.
Lemma lem4412376 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term750 _106189 _106193 A s k x) = (term805 _106189 _106193 A s k x).
Proof. exact (fun_ext (fun y : type804 _106189 _106193 A => @lem4412375 _106189 _106193 A s k x y)). Qed.
Lemma lem4412377 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412378 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term751 _106189 _106193 A s k x) = (term806 _106189 _106193 A s k x).
Proof. exact (MK_COMB (@lem4412377 _106189 _106193 A) (@lem4412376 _106189 _106193 A s k x)). Qed.
Lemma lem4412380 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412381 {_106189 _106193 A : Type'} (P : type201 _106189 _106193 A) : (term807 _106189 _106193 A P) = (term808 _106189 _106193 A P).
Proof. exact (@lem4412380 (type804 _106189 _106193 A) (_106193 -> _106189) P). Qed.
Lemma lem4412382 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term809 _106189 _106193 A s k x) = (term810 _106189 _106193 A s k x).
Proof. exact (@lem4412381 _106189 _106193 A (term811 _106189 _106193 A s k x)). Qed.
Lemma lem4412383 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term812 _106189 _106193 A s k x y) = (term803 _106189 _106193 A s k x y).
Proof. exact (eq_refl (term812 _106189 _106193 A s k x y)). Qed.
Lemma lem4412384 {_106189 _106193 : Type'} (i : _106193 -> _106189) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412385 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) (i : _106193 -> _106189) : (term813 _106189 _106193 A s k x y i) = (term814 _106189 _106193 A s k x y i).
Proof. exact (MK_COMB (@lem4412383 _106189 _106193 A s k x y) (@lem4412384 _106189 _106193 i)). Qed.
Lemma lem4412386 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : _106193 -> _106189) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term814 _106189 _106193 A s k x y i) = (term801 _106189 _106193 A s k i x y).
Proof. exact (eq_refl (term814 _106189 _106193 A s k x y i)). Qed.
Lemma lem4412387 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : _106193 -> _106189) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term813 _106189 _106193 A s k x y i) = (term801 _106189 _106193 A s k i x y).
Proof. exact (TRANS (@lem4412385 _106189 _106193 A s k x y i) (@lem4412386 _106189 _106193 A s k i x y)). Qed.
Lemma lem4412388 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term815 _106189 _106193 A s k x y) = (term803 _106189 _106193 A s k x y).
Proof. exact (fun_ext (fun i : _106193 -> _106189 => @lem4412387 _106189 _106193 A s k i x y)). Qed.
Lemma lem4412389 {_106189 _106193 : Type'} : (@ex (_106193 -> _106189)) = (@ex (_106193 -> _106189)).
Proof. exact (eq_refl (@ex (_106193 -> _106189))). Qed.
Lemma lem4412390 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term816 _106189 _106193 A s k x y) = (term804 _106189 _106193 A s k x y).
Proof. exact (MK_COMB (@lem4412389 _106189 _106193) (@lem4412388 _106189 _106193 A s k x y)). Qed.
Lemma lem4412391 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term817 _106189 _106193 A s k x) = (term805 _106189 _106193 A s k x).
Proof. exact (fun_ext (fun y : type804 _106189 _106193 A => @lem4412390 _106189 _106193 A s k x y)). Qed.
Lemma lem4412392 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412393 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term809 _106189 _106193 A s k x) = (term806 _106189 _106193 A s k x).
Proof. exact (MK_COMB (@lem4412392 _106189 _106193 A) (@lem4412391 _106189 _106193 A s k x)). Qed.
Lemma lem4412394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412395 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term818 _106189 _106193 A s k x) = (term819 _106189 _106193 A s k x).
Proof. exact (MK_COMB (@lem4412394) (@lem4412393 _106189 _106193 A s k x)). Qed.
Lemma lem4412396 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term812 _106189 _106193 A s k x y) = (term803 _106189 _106193 A s k x y).
Proof. exact (eq_refl (term812 _106189 _106193 A s k x y)). Qed.
Lemma lem4412397 {_106189 _106193 A : Type'} (i : type202 _106189 _106193 A) (y : type804 _106189 _106193 A) : (i y) = (i y).
Proof. exact (eq_refl (i y)). Qed.
Lemma lem4412398 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (i : type202 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term820 _106189 _106193 A s k x i y) = (term821 _106189 _106193 A s k x i y).
Proof. exact (MK_COMB (@lem4412396 _106189 _106193 A s k x y) (@lem4412397 _106189 _106193 A i y)). Qed.
Lemma lem4412399 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type202 _106189 _106193 A) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term821 _106189 _106193 A s k x i y) = (term822 _106189 _106193 A s k i x y).
Proof. exact (eq_refl (term821 _106189 _106193 A s k x i y)). Qed.
Lemma lem4412400 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type202 _106189 _106193 A) (x : type804 _106189 _106193 A) (y : type804 _106189 _106193 A) : (term820 _106189 _106193 A s k x i y) = (term822 _106189 _106193 A s k i x y).
Proof. exact (TRANS (@lem4412398 _106189 _106193 A s k x i y) (@lem4412399 _106189 _106193 A s k i x y)). Qed.
Lemma lem4412401 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type202 _106189 _106193 A) (x : type804 _106189 _106193 A) : (term823 _106189 _106193 A s k x i) = (term824 _106189 _106193 A s k i x).
Proof. exact (fun_ext (fun y : type804 _106189 _106193 A => @lem4412400 _106189 _106193 A s k i x y)). Qed.
Lemma lem4412402 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412403 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type202 _106189 _106193 A) (x : type804 _106189 _106193 A) : (term825 _106189 _106193 A s k x i) = (term826 _106189 _106193 A s k i x).
Proof. exact (MK_COMB (@lem4412402 _106189 _106193 A) (@lem4412401 _106189 _106193 A s k i x)). Qed.
Lemma lem4412404 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term827 _106189 _106193 A s k x) = (term828 _106189 _106193 A s k x).
Proof. exact (fun_ext (fun i : type202 _106189 _106193 A => @lem4412403 _106189 _106193 A s k i x)). Qed.
Lemma lem4412405 {_106189 _106193 A : Type'} : (@ex (((_106193 -> _106189) -> A) -> _106193 -> _106189)) = (@ex (((_106193 -> _106189) -> A) -> _106193 -> _106189)).
Proof. exact (eq_refl (@ex (((_106193 -> _106189) -> A) -> _106193 -> _106189))). Qed.
Lemma lem4412406 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term810 _106189 _106193 A s k x) = (term829 _106189 _106193 A s k x).
Proof. exact (MK_COMB (@lem4412405 _106189 _106193 A) (@lem4412404 _106189 _106193 A s k x)). Qed.
Lemma lem4412407 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : ((term809 _106189 _106193 A s k x) = (term810 _106189 _106193 A s k x)) = ((term806 _106189 _106193 A s k x) = (term829 _106189 _106193 A s k x)).
Proof. exact (MK_COMB (@lem4412395 _106189 _106193 A s k x) (@lem4412406 _106189 _106193 A s k x)). Qed.
Lemma lem4412408 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term806 _106189 _106193 A s k x) = (term829 _106189 _106193 A s k x).
Proof. exact (EQ_MP (@lem4412407 _106189 _106193 A s k x) (@lem4412382 _106189 _106193 A s k x)). Qed.
Lemma lem4412409 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term751 _106189 _106193 A s k x) = (term829 _106189 _106193 A s k x).
Proof. exact (TRANS (@lem4412378 _106189 _106193 A s k x) (@lem4412408 _106189 _106193 A s k x)). Qed.
Lemma lem4412410 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term752 _106189 _106193 A s k) = (term830 _106189 _106193 A s k).
Proof. exact (fun_ext (fun x : type804 _106189 _106193 A => @lem4412409 _106189 _106193 A s k x)). Qed.
Lemma lem4412411 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412412 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term753 _106189 _106193 A s k) = (term831 _106189 _106193 A s k).
Proof. exact (MK_COMB (@lem4412411 _106189 _106193 A) (@lem4412410 _106189 _106193 A s k)). Qed.
Lemma lem4412414 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412415 {_106189 _106193 A : Type'} (P : type199 _106189 _106193 A) : (term832 _106189 _106193 A P) = (term833 _106189 _106193 A P).
Proof. exact (@lem4412414 (type804 _106189 _106193 A) (type202 _106189 _106193 A) P). Qed.
Lemma lem4412416 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term834 _106189 _106193 A s k) = (term835 _106189 _106193 A s k).
Proof. exact (@lem4412415 _106189 _106193 A (term836 _106189 _106193 A s k)). Qed.
Lemma lem4412417 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term837 _106189 _106193 A s k x) = (term828 _106189 _106193 A s k x).
Proof. exact (eq_refl (term837 _106189 _106193 A s k x)). Qed.
Lemma lem4412418 {_106189 _106193 A : Type'} (i : type202 _106189 _106193 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412419 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) (i : type202 _106189 _106193 A) : (term838 _106189 _106193 A s k x i) = (term839 _106189 _106193 A s k x i).
Proof. exact (MK_COMB (@lem4412417 _106189 _106193 A s k x) (@lem4412418 _106189 _106193 A i)). Qed.
Lemma lem4412420 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type202 _106189 _106193 A) (x : type804 _106189 _106193 A) : (term839 _106189 _106193 A s k x i) = (term826 _106189 _106193 A s k i x).
Proof. exact (eq_refl (term839 _106189 _106193 A s k x i)). Qed.
Lemma lem4412421 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type202 _106189 _106193 A) (x : type804 _106189 _106193 A) : (term838 _106189 _106193 A s k x i) = (term826 _106189 _106193 A s k i x).
Proof. exact (TRANS (@lem4412419 _106189 _106193 A s k x i) (@lem4412420 _106189 _106193 A s k i x)). Qed.
Lemma lem4412422 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term840 _106189 _106193 A s k x) = (term828 _106189 _106193 A s k x).
Proof. exact (fun_ext (fun i : type202 _106189 _106193 A => @lem4412421 _106189 _106193 A s k i x)). Qed.
Lemma lem4412423 {_106189 _106193 A : Type'} : (@ex (((_106193 -> _106189) -> A) -> _106193 -> _106189)) = (@ex (((_106193 -> _106189) -> A) -> _106193 -> _106189)).
Proof. exact (eq_refl (@ex (((_106193 -> _106189) -> A) -> _106193 -> _106189))). Qed.
Lemma lem4412424 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term841 _106189 _106193 A s k x) = (term829 _106189 _106193 A s k x).
Proof. exact (MK_COMB (@lem4412423 _106189 _106193 A) (@lem4412422 _106189 _106193 A s k x)). Qed.
Lemma lem4412425 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term842 _106189 _106193 A s k) = (term830 _106189 _106193 A s k).
Proof. exact (fun_ext (fun x : type804 _106189 _106193 A => @lem4412424 _106189 _106193 A s k x)). Qed.
Lemma lem4412426 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412427 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term834 _106189 _106193 A s k) = (term831 _106189 _106193 A s k).
Proof. exact (MK_COMB (@lem4412426 _106189 _106193 A) (@lem4412425 _106189 _106193 A s k)). Qed.
Lemma lem4412428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412429 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term843 _106189 _106193 A s k) = (term844 _106189 _106193 A s k).
Proof. exact (MK_COMB (@lem4412428) (@lem4412427 _106189 _106193 A s k)). Qed.
Lemma lem4412430 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (x : type804 _106189 _106193 A) : (term837 _106189 _106193 A s k x) = (term828 _106189 _106193 A s k x).
Proof. exact (eq_refl (term837 _106189 _106193 A s k x)). Qed.
Lemma lem4412431 {_106189 _106193 A : Type'} (i : type200 _106189 _106193 A) (x : type804 _106189 _106193 A) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem4412432 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) (x : type804 _106189 _106193 A) : (term845 _106189 _106193 A s k i x) = (term846 _106189 _106193 A s k i x).
Proof. exact (MK_COMB (@lem4412430 _106189 _106193 A s k x) (@lem4412431 _106189 _106193 A i x)). Qed.
Lemma lem4412433 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) (x : type804 _106189 _106193 A) : (term846 _106189 _106193 A s k i x) = (term847 _106189 _106193 A s k i x).
Proof. exact (eq_refl (term846 _106189 _106193 A s k i x)). Qed.
Lemma lem4412434 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) (x : type804 _106189 _106193 A) : (term845 _106189 _106193 A s k i x) = (term847 _106189 _106193 A s k i x).
Proof. exact (TRANS (@lem4412432 _106189 _106193 A s k i x) (@lem4412433 _106189 _106193 A s k i x)). Qed.
Lemma lem4412435 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) : (term848 _106189 _106193 A s k i) = (term849 _106189 _106193 A s k i).
Proof. exact (fun_ext (fun x : type804 _106189 _106193 A => @lem4412434 _106189 _106193 A s k i x)). Qed.
Lemma lem4412436 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A)) = (@all ((_106193 -> _106189) -> A)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A))). Qed.
Lemma lem4412437 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) : (term850 _106189 _106193 A s k i) = (term851 _106189 _106193 A s k i).
Proof. exact (MK_COMB (@lem4412436 _106189 _106193 A) (@lem4412435 _106189 _106193 A s k i)). Qed.
Lemma lem4412438 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term852 _106189 _106193 A s k) = (term853 _106189 _106193 A s k).
Proof. exact (fun_ext (fun i : type200 _106189 _106193 A => @lem4412437 _106189 _106193 A s k i)). Qed.
Lemma lem4412439 {_106189 _106193 A : Type'} : (@ex (((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)) = (@ex (((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)).
Proof. exact (eq_refl (@ex (((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189))). Qed.
Lemma lem4412440 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term835 _106189 _106193 A s k) = (term854 _106189 _106193 A s k).
Proof. exact (MK_COMB (@lem4412439 _106189 _106193 A) (@lem4412438 _106189 _106193 A s k)). Qed.
Lemma lem4412441 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : ((term834 _106189 _106193 A s k) = (term835 _106189 _106193 A s k)) = ((term831 _106189 _106193 A s k) = (term854 _106189 _106193 A s k)).
Proof. exact (MK_COMB (@lem4412429 _106189 _106193 A s k) (@lem4412440 _106189 _106193 A s k)). Qed.
Lemma lem4412442 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term831 _106189 _106193 A s k) = (term854 _106189 _106193 A s k).
Proof. exact (EQ_MP (@lem4412441 _106189 _106193 A s k) (@lem4412416 _106189 _106193 A s k)). Qed.
Lemma lem4412443 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term753 _106189 _106193 A s k) = (term854 _106189 _106193 A s k).
Proof. exact (TRANS (@lem4412412 _106189 _106193 A s k) (@lem4412442 _106189 _106193 A s k)). Qed.
Lemma lem4412444 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term754 _106189 _106193 A k) = (term855 _106189 _106193 A k).
Proof. exact (fun_ext (fun s : type800 _106189 _106193 A => @lem4412443 _106189 _106193 A s k)). Qed.
Lemma lem4412445 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A -> Prop)) = (@all ((_106193 -> _106189) -> A -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A -> Prop))). Qed.
Lemma lem4412446 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term755 _106189 _106193 A k) = (term856 _106189 _106193 A k).
Proof. exact (MK_COMB (@lem4412445 _106189 _106193 A) (@lem4412444 _106189 _106193 A k)). Qed.
Lemma lem4412448 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412449 {_106189 _106193 A : Type'} (P : type195 _106189 _106193 A) : (term857 _106189 _106193 A P) = (term858 _106189 _106193 A P).
Proof. exact (@lem4412448 (type800 _106189 _106193 A) (type200 _106189 _106193 A) P). Qed.
Lemma lem4412450 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term859 _106189 _106193 A k) = (term860 _106189 _106193 A k).
Proof. exact (@lem4412449 _106189 _106193 A (term861 _106189 _106193 A k)). Qed.
Lemma lem4412451 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term862 _106189 _106193 A k s) = (term853 _106189 _106193 A s k).
Proof. exact (eq_refl (term862 _106189 _106193 A k s)). Qed.
Lemma lem4412452 {_106189 _106193 A : Type'} (i : type200 _106189 _106193 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412453 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) : (term863 _106189 _106193 A k s i) = (term864 _106189 _106193 A s k i).
Proof. exact (MK_COMB (@lem4412451 _106189 _106193 A s k) (@lem4412452 _106189 _106193 A i)). Qed.
Lemma lem4412454 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) : (term864 _106189 _106193 A s k i) = (term851 _106189 _106193 A s k i).
Proof. exact (eq_refl (term864 _106189 _106193 A s k i)). Qed.
Lemma lem4412455 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) (i : type200 _106189 _106193 A) : (term863 _106189 _106193 A k s i) = (term851 _106189 _106193 A s k i).
Proof. exact (TRANS (@lem4412453 _106189 _106193 A s k i) (@lem4412454 _106189 _106193 A s k i)). Qed.
Lemma lem4412456 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term865 _106189 _106193 A k s) = (term853 _106189 _106193 A s k).
Proof. exact (fun_ext (fun i : type200 _106189 _106193 A => @lem4412455 _106189 _106193 A s k i)). Qed.
Lemma lem4412457 {_106189 _106193 A : Type'} : (@ex (((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)) = (@ex (((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)).
Proof. exact (eq_refl (@ex (((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189))). Qed.
Lemma lem4412458 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term866 _106189 _106193 A k s) = (term854 _106189 _106193 A s k).
Proof. exact (MK_COMB (@lem4412457 _106189 _106193 A) (@lem4412456 _106189 _106193 A s k)). Qed.
Lemma lem4412459 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term867 _106189 _106193 A k) = (term855 _106189 _106193 A k).
Proof. exact (fun_ext (fun s : type800 _106189 _106193 A => @lem4412458 _106189 _106193 A s k)). Qed.
Lemma lem4412460 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A -> Prop)) = (@all ((_106193 -> _106189) -> A -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A -> Prop))). Qed.
Lemma lem4412461 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term859 _106189 _106193 A k) = (term856 _106189 _106193 A k).
Proof. exact (MK_COMB (@lem4412460 _106189 _106193 A) (@lem4412459 _106189 _106193 A k)). Qed.
Lemma lem4412462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412463 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term868 _106189 _106193 A k) = (term869 _106189 _106193 A k).
Proof. exact (MK_COMB (@lem4412462) (@lem4412461 _106189 _106193 A k)). Qed.
Lemma lem4412464 {_106189 _106193 A : Type'} (s : type800 _106189 _106193 A) (k : type805 _106189 _106193) : (term862 _106189 _106193 A k s) = (term853 _106189 _106193 A s k).
Proof. exact (eq_refl (term862 _106189 _106193 A k s)). Qed.
Lemma lem4412465 {_106189 _106193 A : Type'} (i : type196 _106189 _106193 A) (s : type800 _106189 _106193 A) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem4412466 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) (s : type800 _106189 _106193 A) : (term870 _106189 _106193 A k i s) = (term871 _106189 _106193 A k i s).
Proof. exact (MK_COMB (@lem4412464 _106189 _106193 A s k) (@lem4412465 _106189 _106193 A i s)). Qed.
Lemma lem4412467 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) (s : type800 _106189 _106193 A) : (term871 _106189 _106193 A k i s) = (term872 _106189 _106193 A k i s).
Proof. exact (eq_refl (term871 _106189 _106193 A k i s)). Qed.
Lemma lem4412468 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) (s : type800 _106189 _106193 A) : (term870 _106189 _106193 A k i s) = (term872 _106189 _106193 A k i s).
Proof. exact (TRANS (@lem4412466 _106189 _106193 A k i s) (@lem4412467 _106189 _106193 A k i s)). Qed.
Lemma lem4412469 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) : (term873 _106189 _106193 A k i) = (term874 _106189 _106193 A k i).
Proof. exact (fun_ext (fun s : type800 _106189 _106193 A => @lem4412468 _106189 _106193 A k i s)). Qed.
Lemma lem4412470 {_106189 _106193 A : Type'} : (@all ((_106193 -> _106189) -> A -> Prop)) = (@all ((_106193 -> _106189) -> A -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> A -> Prop))). Qed.
Lemma lem4412471 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) : (term875 _106189 _106193 A k i) = (term876 _106189 _106193 A k i).
Proof. exact (MK_COMB (@lem4412470 _106189 _106193 A) (@lem4412469 _106189 _106193 A k i)). Qed.
Lemma lem4412472 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term877 _106189 _106193 A k) = (term878 _106189 _106193 A k).
Proof. exact (fun_ext (fun i : type196 _106189 _106193 A => @lem4412471 _106189 _106193 A k i)). Qed.
Lemma lem4412473 {_106189 _106193 A : Type'} : (@ex (((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)) = (@ex (((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)).
Proof. exact (eq_refl (@ex (((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189))). Qed.
Lemma lem4412474 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term860 _106189 _106193 A k) = (term879 _106189 _106193 A k).
Proof. exact (MK_COMB (@lem4412473 _106189 _106193 A) (@lem4412472 _106189 _106193 A k)). Qed.
Lemma lem4412475 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : ((term859 _106189 _106193 A k) = (term860 _106189 _106193 A k)) = ((term856 _106189 _106193 A k) = (term879 _106189 _106193 A k)).
Proof. exact (MK_COMB (@lem4412463 _106189 _106193 A k) (@lem4412474 _106189 _106193 A k)). Qed.
Lemma lem4412476 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term856 _106189 _106193 A k) = (term879 _106189 _106193 A k).
Proof. exact (EQ_MP (@lem4412475 _106189 _106193 A k) (@lem4412450 _106189 _106193 A k)). Qed.
Lemma lem4412477 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term755 _106189 _106193 A k) = (term879 _106189 _106193 A k).
Proof. exact (TRANS (@lem4412446 _106189 _106193 A k) (@lem4412476 _106189 _106193 A k)). Qed.
Lemma lem4412478 {_106189 _106193 A : Type'} : (term756 _106189 _106193 A) = (term880 _106189 _106193 A).
Proof. exact (fun_ext (fun k : type805 _106189 _106193 => @lem4412477 _106189 _106193 A k)). Qed.
Lemma lem4412479 {_106189 _106193 : Type'} : (@all ((_106193 -> _106189) -> Prop)) = (@all ((_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> Prop))). Qed.
Lemma lem4412480 {_106189 _106193 A : Type'} : (term757 _106189 _106193 A) = (term881 _106189 _106193 A).
Proof. exact (MK_COMB (@lem4412479 _106189 _106193) (@lem4412478 _106189 _106193 A)). Qed.
Lemma lem4412482 {A B : Type'} (P : type1413 A B) : (term285 A B P) = (term286 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4412483 {_106189 _106193 A : Type'} (P : type203 _106189 _106193 A) : (term882 _106189 _106193 A P) = (term883 _106189 _106193 A P).
Proof. exact (@lem4412482 (type805 _106189 _106193) (type196 _106189 _106193 A) P). Qed.
Lemma lem4412484 {_106189 _106193 A : Type'} : (term884 _106189 _106193 A) = (term885 _106189 _106193 A).
Proof. exact (@lem4412483 _106189 _106193 A (term886 _106189 _106193 A)). Qed.
Lemma lem4412485 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term887 _106189 _106193 A k) = (term878 _106189 _106193 A k).
Proof. exact (eq_refl (term887 _106189 _106193 A k)). Qed.
Lemma lem4412486 {_106189 _106193 A : Type'} (i : type196 _106189 _106193 A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4412487 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) : (term888 _106189 _106193 A k i) = (term889 _106189 _106193 A k i).
Proof. exact (MK_COMB (@lem4412485 _106189 _106193 A k) (@lem4412486 _106189 _106193 A i)). Qed.
Lemma lem4412488 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) : (term889 _106189 _106193 A k i) = (term876 _106189 _106193 A k i).
Proof. exact (eq_refl (term889 _106189 _106193 A k i)). Qed.
Lemma lem4412489 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) (i : type196 _106189 _106193 A) : (term888 _106189 _106193 A k i) = (term876 _106189 _106193 A k i).
Proof. exact (TRANS (@lem4412487 _106189 _106193 A k i) (@lem4412488 _106189 _106193 A k i)). Qed.
Lemma lem4412490 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term890 _106189 _106193 A k) = (term878 _106189 _106193 A k).
Proof. exact (fun_ext (fun i : type196 _106189 _106193 A => @lem4412489 _106189 _106193 A k i)). Qed.
Lemma lem4412491 {_106189 _106193 A : Type'} : (@ex (((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)) = (@ex (((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)).
Proof. exact (eq_refl (@ex (((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189))). Qed.
Lemma lem4412492 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term891 _106189 _106193 A k) = (term879 _106189 _106193 A k).
Proof. exact (MK_COMB (@lem4412491 _106189 _106193 A) (@lem4412490 _106189 _106193 A k)). Qed.
Lemma lem4412493 {_106189 _106193 A : Type'} : (term892 _106189 _106193 A) = (term880 _106189 _106193 A).
Proof. exact (fun_ext (fun k : type805 _106189 _106193 => @lem4412492 _106189 _106193 A k)). Qed.
Lemma lem4412494 {_106189 _106193 : Type'} : (@all ((_106193 -> _106189) -> Prop)) = (@all ((_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> Prop))). Qed.
Lemma lem4412495 {_106189 _106193 A : Type'} : (term884 _106189 _106193 A) = (term881 _106189 _106193 A).
Proof. exact (MK_COMB (@lem4412494 _106189 _106193) (@lem4412493 _106189 _106193 A)). Qed.
Lemma lem4412496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4412497 {_106189 _106193 A : Type'} : (term893 _106189 _106193 A) = (term894 _106189 _106193 A).
Proof. exact (MK_COMB (@lem4412496) (@lem4412495 _106189 _106193 A)). Qed.
Lemma lem4412498 {_106189 _106193 A : Type'} (k : type805 _106189 _106193) : (term887 _106189 _106193 A k) = (term878 _106189 _106193 A k).
Proof. exact (eq_refl (term887 _106189 _106193 A k)). Qed.
Lemma lem4412499 {_106189 _106193 A : Type'} (i : type204 _106189 _106193 A) (k : type805 _106189 _106193) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem4412500 {_106189 _106193 A : Type'} (i : type204 _106189 _106193 A) (k : type805 _106189 _106193) : (term895 _106189 _106193 A i k) = (term896 _106189 _106193 A i k).
Proof. exact (MK_COMB (@lem4412498 _106189 _106193 A k) (@lem4412499 _106189 _106193 A i k)). Qed.
Lemma lem4412501 {_106189 _106193 A : Type'} (i : type204 _106189 _106193 A) (k : type805 _106189 _106193) : (term896 _106189 _106193 A i k) = (term897 _106189 _106193 A i k).
Proof. exact (eq_refl (term896 _106189 _106193 A i k)). Qed.
Lemma lem4412502 {_106189 _106193 A : Type'} (i : type204 _106189 _106193 A) (k : type805 _106189 _106193) : (term895 _106189 _106193 A i k) = (term897 _106189 _106193 A i k).
Proof. exact (TRANS (@lem4412500 _106189 _106193 A i k) (@lem4412501 _106189 _106193 A i k)). Qed.
Lemma lem4412503 {_106189 _106193 A : Type'} (i : type204 _106189 _106193 A) : (term898 _106189 _106193 A i) = (term899 _106189 _106193 A i).
Proof. exact (fun_ext (fun k : type805 _106189 _106193 => @lem4412502 _106189 _106193 A i k)). Qed.
Lemma lem4412504 {_106189 _106193 : Type'} : (@all ((_106193 -> _106189) -> Prop)) = (@all ((_106193 -> _106189) -> Prop)).
Proof. exact (eq_refl (@all ((_106193 -> _106189) -> Prop))). Qed.
Lemma lem4412505 {_106189 _106193 A : Type'} (i : type204 _106189 _106193 A) : (term900 _106189 _106193 A i) = (term901 _106189 _106193 A i).
Proof. exact (MK_COMB (@lem4412504 _106189 _106193) (@lem4412503 _106189 _106193 A i)). Qed.
Lemma lem4412506 {_106189 _106193 A : Type'} : (term902 _106189 _106193 A) = (term903 _106189 _106193 A).
Proof. exact (fun_ext (fun i : type204 _106189 _106193 A => @lem4412505 _106189 _106193 A i)). Qed.
Lemma lem4412507 {_106189 _106193 A : Type'} : (@ex (((_106193 -> _106189) -> Prop) -> ((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)) = (@ex (((_106193 -> _106189) -> Prop) -> ((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189)).
Proof. exact (eq_refl (@ex (((_106193 -> _106189) -> Prop) -> ((_106193 -> _106189) -> A -> Prop) -> ((_106193 -> _106189) -> A) -> ((_106193 -> _106189) -> A) -> _106193 -> _106189))). Qed.
Lemma lem4412508 {_106189 _106193 A : Type'} : (term885 _106189 _106193 A) = (term904 _106189 _106193 A).
Proof. exact (MK_COMB (@lem4412507 _106189 _106193 A) (@lem4412506 _106189 _106193 A)). Qed.
Lemma lem4412509 {_106189 _106193 A : Type'} : ((term884 _106189 _106193 A) = (term885 _106189 _106193 A)) = ((term881 _106189 _106193 A) = (term904 _106189 _106193 A)).
Proof. exact (MK_COMB (@lem4412497 _106189 _106193 A) (@lem4412508 _106189 _106193 A)). Qed.
Lemma lem4412510 {_106189 _106193 A : Type'} : (term881 _106189 _106193 A) = (term904 _106189 _106193 A).
Proof. exact (EQ_MP (@lem4412509 _106189 _106193 A) (@lem4412484 _106189 _106193 A)). Qed.
Lemma lem4412512 {_106189 _106193 A : Type'} : (term757 _106189 _106193 A) = (term904 _106189 _106193 A).
Proof. exact (TRANS (@lem4412480 _106189 _106193 A) (@lem4412510 _106189 _106193 A)). Qed.
Lemma lem4412513 {_106189 _106193 A : Type'} : (term12 _106189 _106193 A) = (term904 _106189 _106193 A).
Proof. exact (TRANS (@lem4412194 _106189 _106193 A) (@lem4412512 _106189 _106193 A)). Qed.
Lemma lem4412514 {_106189 _106193 A : Type'} (h1 : term12 _106189 _106193 A) : term904 _106189 _106193 A.
Proof. exact (EQ_MP (@lem4412513 _106189 _106193 A) (@lem4410345 _106189 _106193 A h1)). Qed.
Lemma lem4412519 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term381 _106189 _106193 i''''.
Proof. exact (h1). Qed.
Lemma lem4412520 {_106189 _106193 : Type'} (k : _106193 -> Prop) (h1 : term218 _106189 _106193 k) : term218 _106189 _106193 k.
Proof. exact (h1). Qed.
Lemma lem4412521 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (h1 : term216 _106189 _106193 s k) : term216 _106189 _106193 s k.
Proof. exact (h1). Qed.
Lemma lem4412522 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (h1 : term214 _106189 _106193 s k x) : term214 _106189 _106193 s k x.
Proof. exact (h1). Qed.
Lemma lem4412523 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term212 _106189 _106193 s k x y) : term212 _106189 _106193 s k x y.
Proof. exact (h1). Qed.
Lemma lem4412524 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term209 _106189 _106193 s i''''' k x y.
Proof. exact (h1). Qed.
Lemma lem4413489 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4413490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4413491 {_106189 : Type'} : (@eq _106189) = (@eq _106189).
Proof. exact (eq_refl (@eq _106189)). Qed.
Lemma lem4413492 {_106189 _106193 : Type'} (x : _106193 -> _106189) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4413503 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413504 {_106189 _106193 : Type'} (f : type844 _106189 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413503 (_106193 -> Prop) (type733 _106189 _106193) f x). Qed.
Lemma lem4413505 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) : (i'''' k) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k).
Proof. exact (@lem4413504 _106189 _106193 i'''' k). Qed.
Lemma lem4413506 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4413507 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (i'''' k s) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k s).
Proof. exact (MK_COMB (@lem4413505 _106189 _106193 i'''' k) (@lem4413506 _106189 _106193 s)). Qed.
Lemma lem4413509 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413510 {_106189 _106193 : Type'} (f : type733 _106189 _106193) (x : type1470 _106189 _106193) : (f x) = (@I ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413509 (type1470 _106189 _106193) (type785 _106189 _106193) f x). Qed.
Lemma lem4413511 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k s) = (term905 _106189 _106193 i'''' k s).
Proof. exact (@lem4413510 _106189 _106193 (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k) s). Qed.
Lemma lem4413512 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (i'''' k s) = (term905 _106189 _106193 i'''' k s).
Proof. exact (TRANS (@lem4413507 _106189 _106193 i'''' k s) (@lem4413511 _106189 _106193 i'''' k s)). Qed.
Lemma lem4413513 {_106189 _106193 : Type'} (x : _106193 -> _106189) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4413514 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (i'''' k s x) = (term906 _106189 _106193 i'''' k s x).
Proof. exact (MK_COMB (@lem4413512 _106189 _106193 i'''' k s) (@lem4413513 _106189 _106193 x)). Qed.
Lemma lem4413516 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413517 {_106189 _106193 : Type'} (f : type785 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413516 (_106193 -> _106189) (type803 _106189 _106193) f x). Qed.
Lemma lem4413518 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (term906 _106189 _106193 i'''' k s x) = (term907 _106189 _106193 i'''' k s x).
Proof. exact (@lem4413517 _106189 _106193 (term905 _106189 _106193 i'''' k s) x). Qed.
Lemma lem4413519 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (i'''' k s x) = (term907 _106189 _106193 i'''' k s x).
Proof. exact (TRANS (@lem4413514 _106189 _106193 i'''' k s x) (@lem4413518 _106189 _106193 i'''' k s x)). Qed.
Lemma lem4413520 {_106189 _106193 : Type'} (y : _106193 -> _106189) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4413521 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (i'''' k s x y) = (term908 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413519 _106189 _106193 i'''' k s x) (@lem4413520 _106189 _106193 y)). Qed.
Lemma lem4413523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413524 {_106189 _106193 : Type'} (f : type803 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413523 (_106193 -> _106189) _106193 f x). Qed.
Lemma lem4413525 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term908 _106189 _106193 i'''' k s x y) = (term909 _106189 _106193 i'''' k s x y).
Proof. exact (@lem4413524 _106189 _106193 (term907 _106189 _106193 i'''' k s x) y). Qed.
Lemma lem4413527 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (i'''' k s x y) = (term909 _106189 _106193 i'''' k s x y).
Proof. exact (TRANS (@lem4413521 _106189 _106193 i'''' k s x y) (@lem4413525 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413528 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term910 _106189 _106193 i'''' k s x y) = (term911 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413492 _106189 _106193 x) (@lem4413527 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413530 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413531 {_106189 _106193 : Type'} (f : _106193 -> _106189) (x : _106193) : (f x) = (@I (_106193 -> _106189) f x).
Proof. exact (@lem4413530 _106193 _106189 f x). Qed.
Lemma lem4413532 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term911 _106189 _106193 i'''' k s x y) = (term912 _106189 _106193 i'''' k s x y).
Proof. exact (@lem4413531 _106189 _106193 x (term909 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413533 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term910 _106189 _106193 i'''' k s x y) = (term912 _106189 _106193 i'''' k s x y).
Proof. exact (TRANS (@lem4413528 _106189 _106193 i'''' k s x y) (@lem4413532 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413534 {_106189 _106193 : Type'} (y : _106193 -> _106189) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4413545 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413546 {_106189 _106193 : Type'} (f : type844 _106189 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413545 (_106193 -> Prop) (type733 _106189 _106193) f x). Qed.
Lemma lem4413547 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) : (i'''' k) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k).
Proof. exact (@lem4413546 _106189 _106193 i'''' k). Qed.
Lemma lem4413548 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4413549 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (i'''' k s) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k s).
Proof. exact (MK_COMB (@lem4413547 _106189 _106193 i'''' k) (@lem4413548 _106189 _106193 s)). Qed.
Lemma lem4413551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413552 {_106189 _106193 : Type'} (f : type733 _106189 _106193) (x : type1470 _106189 _106193) : (f x) = (@I ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413551 (type1470 _106189 _106193) (type785 _106189 _106193) f x). Qed.
Lemma lem4413553 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k s) = (term905 _106189 _106193 i'''' k s).
Proof. exact (@lem4413552 _106189 _106193 (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k) s). Qed.
Lemma lem4413554 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (i'''' k s) = (term905 _106189 _106193 i'''' k s).
Proof. exact (TRANS (@lem4413549 _106189 _106193 i'''' k s) (@lem4413553 _106189 _106193 i'''' k s)). Qed.
Lemma lem4413555 {_106189 _106193 : Type'} (x : _106193 -> _106189) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4413556 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (i'''' k s x) = (term906 _106189 _106193 i'''' k s x).
Proof. exact (MK_COMB (@lem4413554 _106189 _106193 i'''' k s) (@lem4413555 _106189 _106193 x)). Qed.
Lemma lem4413558 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413559 {_106189 _106193 : Type'} (f : type785 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413558 (_106193 -> _106189) (type803 _106189 _106193) f x). Qed.
Lemma lem4413560 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (term906 _106189 _106193 i'''' k s x) = (term907 _106189 _106193 i'''' k s x).
Proof. exact (@lem4413559 _106189 _106193 (term905 _106189 _106193 i'''' k s) x). Qed.
Lemma lem4413561 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (i'''' k s x) = (term907 _106189 _106193 i'''' k s x).
Proof. exact (TRANS (@lem4413556 _106189 _106193 i'''' k s x) (@lem4413560 _106189 _106193 i'''' k s x)). Qed.
Lemma lem4413562 {_106189 _106193 : Type'} (y : _106193 -> _106189) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4413563 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (i'''' k s x y) = (term908 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413561 _106189 _106193 i'''' k s x) (@lem4413562 _106189 _106193 y)). Qed.
Lemma lem4413565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413566 {_106189 _106193 : Type'} (f : type803 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413565 (_106193 -> _106189) _106193 f x). Qed.
Lemma lem4413567 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term908 _106189 _106193 i'''' k s x y) = (term909 _106189 _106193 i'''' k s x y).
Proof. exact (@lem4413566 _106189 _106193 (term907 _106189 _106193 i'''' k s x) y). Qed.
Lemma lem4413569 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (i'''' k s x y) = (term909 _106189 _106193 i'''' k s x y).
Proof. exact (TRANS (@lem4413563 _106189 _106193 i'''' k s x y) (@lem4413567 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413570 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term913 _106189 _106193 i'''' k s x y) = (term914 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413534 _106189 _106193 y) (@lem4413569 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413572 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413573 {_106189 _106193 : Type'} (f : _106193 -> _106189) (x : _106193) : (f x) = (@I (_106193 -> _106189) f x).
Proof. exact (@lem4413572 _106193 _106189 f x). Qed.
Lemma lem4413574 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term914 _106189 _106193 i'''' k s x y) = (term915 _106189 _106193 i'''' k s x y).
Proof. exact (@lem4413573 _106189 _106193 y (term909 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413575 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term913 _106189 _106193 i'''' k s x y) = (term915 _106189 _106193 i'''' k s x y).
Proof. exact (TRANS (@lem4413570 _106189 _106193 i'''' k s x y) (@lem4413574 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413576 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term916 _106189 _106193 i'''' k s x y) = (term917 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413491 _106189) (@lem4413533 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413577 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : ((term910 _106189 _106193 i'''' k s x y) = (term913 _106189 _106193 i'''' k s x y)) = ((term912 _106189 _106193 i'''' k s x y) = (term915 _106189 _106193 i'''' k s x y)).
Proof. exact (MK_COMB (@lem4413576 _106189 _106193 i'''' k s x y) (@lem4413575 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413578 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term918 _106189 _106193 i'''' k s x y) = (term919 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413490) (@lem4413577 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413579 {_106193 : Type'} : (@IN _106193) = (@IN _106193).
Proof. exact (eq_refl (@IN _106193)). Qed.
Lemma lem4413590 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413591 {_106189 _106193 : Type'} (f : type844 _106189 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413590 (_106193 -> Prop) (type733 _106189 _106193) f x). Qed.
Lemma lem4413592 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) : (i'''' k) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k).
Proof. exact (@lem4413591 _106189 _106193 i'''' k). Qed.
Lemma lem4413593 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4413594 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (i'''' k s) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k s).
Proof. exact (MK_COMB (@lem4413592 _106189 _106193 i'''' k) (@lem4413593 _106189 _106193 s)). Qed.
Lemma lem4413596 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413597 {_106189 _106193 : Type'} (f : type733 _106189 _106193) (x : type1470 _106189 _106193) : (f x) = (@I ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413596 (type1470 _106189 _106193) (type785 _106189 _106193) f x). Qed.
Lemma lem4413598 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k s) = (term905 _106189 _106193 i'''' k s).
Proof. exact (@lem4413597 _106189 _106193 (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> (_106193 -> _106189) -> _106193) i'''' k) s). Qed.
Lemma lem4413599 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (i'''' k s) = (term905 _106189 _106193 i'''' k s).
Proof. exact (TRANS (@lem4413594 _106189 _106193 i'''' k s) (@lem4413598 _106189 _106193 i'''' k s)). Qed.
Lemma lem4413600 {_106189 _106193 : Type'} (x : _106193 -> _106189) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4413601 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (i'''' k s x) = (term906 _106189 _106193 i'''' k s x).
Proof. exact (MK_COMB (@lem4413599 _106189 _106193 i'''' k s) (@lem4413600 _106189 _106193 x)). Qed.
Lemma lem4413603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413604 {_106189 _106193 : Type'} (f : type785 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> (_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413603 (_106193 -> _106189) (type803 _106189 _106193) f x). Qed.
Lemma lem4413605 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (term906 _106189 _106193 i'''' k s x) = (term907 _106189 _106193 i'''' k s x).
Proof. exact (@lem4413604 _106189 _106193 (term905 _106189 _106193 i'''' k s) x). Qed.
Lemma lem4413606 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (i'''' k s x) = (term907 _106189 _106193 i'''' k s x).
Proof. exact (TRANS (@lem4413601 _106189 _106193 i'''' k s x) (@lem4413605 _106189 _106193 i'''' k s x)). Qed.
Lemma lem4413607 {_106189 _106193 : Type'} (y : _106193 -> _106189) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4413608 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (i'''' k s x y) = (term908 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413606 _106189 _106193 i'''' k s x) (@lem4413607 _106189 _106193 y)). Qed.
Lemma lem4413610 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413611 {_106189 _106193 : Type'} (f : type803 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> _106193) f x).
Proof. exact (@lem4413610 (_106193 -> _106189) _106193 f x). Qed.
Lemma lem4413612 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term908 _106189 _106193 i'''' k s x y) = (term909 _106189 _106193 i'''' k s x y).
Proof. exact (@lem4413611 _106189 _106193 (term907 _106189 _106193 i'''' k s x) y). Qed.
Lemma lem4413614 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (i'''' k s x y) = (term909 _106189 _106193 i'''' k s x y).
Proof. exact (TRANS (@lem4413608 _106189 _106193 i'''' k s x y) (@lem4413612 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413615 {_106193 : Type'} (k : _106193 -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4413616 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term920 _106189 _106193 i'''' k s x y) = (term921 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413579 _106193) (@lem4413614 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413617 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) : (term922 _106189 _106193 i'''' s x y k) = (term923 _106189 _106193 i'''' s x y k).
Proof. exact (MK_COMB (@lem4413616 _106189 _106193 i'''' k s x y) (@lem4413615 _106193 k)). Qed.
Lemma lem4413619 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413620 {_106193 : Type'} (f : type1364 _106193) (x : _106193) : (f x) = (@I (_106193 -> (_106193 -> Prop) -> Prop) f x).
Proof. exact (@lem4413619 _106193 (type686 _106193) f x). Qed.
Lemma lem4413621 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term921 _106189 _106193 i'''' k s x y) = (term924 _106189 _106193 i'''' k s x y).
Proof. exact (@lem4413620 _106193 (@IN _106193) (term909 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413622 {_106193 : Type'} (k : _106193 -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4413623 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) : (term923 _106189 _106193 i'''' s x y k) = (term925 _106189 _106193 i'''' s x y k).
Proof. exact (MK_COMB (@lem4413621 _106189 _106193 i'''' k s x y) (@lem4413622 _106193 k)). Qed.
Lemma lem4413625 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413626 {_106193 : Type'} (f : type686 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> Prop) f x).
Proof. exact (@lem4413625 (_106193 -> Prop) Prop f x). Qed.
Lemma lem4413627 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) : (term925 _106189 _106193 i'''' s x y k) = (term926 _106189 _106193 i'''' s x y k).
Proof. exact (@lem4413626 _106193 (term924 _106189 _106193 i'''' k s x y) k). Qed.
Lemma lem4413628 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) : (term923 _106189 _106193 i'''' s x y k) = (term926 _106189 _106193 i'''' s x y k).
Proof. exact (TRANS (@lem4413623 _106189 _106193 i'''' s x y k) (@lem4413627 _106189 _106193 i'''' s x y k)). Qed.
Lemma lem4413629 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) : (term922 _106189 _106193 i'''' s x y k) = (term926 _106189 _106193 i'''' s x y k).
Proof. exact (TRANS (@lem4413617 _106189 _106193 i'''' s x y k) (@lem4413628 _106189 _106193 i'''' s x y k)). Qed.
Lemma lem4413630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4413631 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) : (term927 _106189 _106193 i'''' s x y k) = (term928 _106189 _106193 i'''' s x y k).
Proof. exact (MK_COMB (@lem4413630) (@lem4413629 _106189 _106193 i'''' s x y k)). Qed.
Lemma lem4413632 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term929 _106189 _106193 i'''' k s x y) = (term930 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413631 _106189 _106193 i'''' s x y k) (@lem4413578 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413633 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4413642 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413643 {_106189 _106193 : Type'} (f : type845 _106189 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413642 (_106193 -> Prop) (type734 _106189 _106193) f x). Qed.
Lemma lem4413644 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (@cartesian_product _106189 _106193 k) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k).
Proof. exact (@lem4413643 _106189 _106193 (@cartesian_product _106189 _106193) k). Qed.
Lemma lem4413645 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4413646 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s).
Proof. exact (MK_COMB (@lem4413644 _106189 _106193 k) (@lem4413645 _106189 _106193 s)). Qed.
Lemma lem4413648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413649 {_106189 _106193 : Type'} (f : type734 _106189 _106193) (x : type1470 _106189 _106193) : (f x) = (@I ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413648 (type1470 _106189 _106193) (type805 _106189 _106193) f x). Qed.
Lemma lem4413650 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s) = (term931 _106189 _106193 k s).
Proof. exact (@lem4413649 _106189 _106193 (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k) s). Qed.
Lemma lem4413652 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (TRANS (@lem4413646 _106189 _106193 k s) (@lem4413650 _106189 _106193 k s)). Qed.
Lemma lem4413653 {_106189 _106193 : Type'} (y : _106193 -> _106189) : (@IN (_106193 -> _106189) y) = (@IN (_106193 -> _106189) y).
Proof. exact (eq_refl (@IN (_106193 -> _106189) y)). Qed.
Lemma lem4413654 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 y k s) = (term932 _106189 _106193 y k s).
Proof. exact (MK_COMB (@lem4413653 _106189 _106193 y) (@lem4413652 _106189 _106193 k s)). Qed.
Lemma lem4413656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413657 {_106189 _106193 : Type'} (f : type773 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413656 (_106193 -> _106189) (type207 _106189 _106193) f x). Qed.
Lemma lem4413658 {_106189 _106193 : Type'} (y : _106193 -> _106189) : (@IN (_106193 -> _106189) y) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) y).
Proof. exact (@lem4413657 _106189 _106193 (@IN (_106193 -> _106189)) y). Qed.
Lemma lem4413659 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term931 _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (eq_refl (term931 _106189 _106193 k s)). Qed.
Lemma lem4413660 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 y k s) = (term933 _106189 _106193 y k s).
Proof. exact (MK_COMB (@lem4413658 _106189 _106193 y) (@lem4413659 _106189 _106193 k s)). Qed.
Lemma lem4413662 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413663 {_106189 _106193 : Type'} (f : type207 _106189 _106193) (x : type805 _106189 _106193) : (f x) = (@I (((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413662 (type805 _106189 _106193) Prop f x). Qed.
Lemma lem4413664 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term933 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (@lem4413663 _106189 _106193 (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) y) (term931 _106189 _106193 k s)). Qed.
Lemma lem4413665 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (TRANS (@lem4413660 _106189 _106193 y k s) (@lem4413664 _106189 _106193 y k s)). Qed.
Lemma lem4413666 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (TRANS (@lem4413654 _106189 _106193 y k s) (@lem4413665 _106189 _106193 y k s)). Qed.
Lemma lem4413667 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term245 _106189 _106193 y k s) = (term935 _106189 _106193 y k s).
Proof. exact (MK_COMB (@lem4413633) (@lem4413666 _106189 _106193 y k s)). Qed.
Lemma lem4413668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4413669 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 y k s) = (term936 _106189 _106193 y k s).
Proof. exact (MK_COMB (@lem4413668) (@lem4413667 _106189 _106193 y k s)). Qed.
Lemma lem4413670 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term937 _106189 _106193 i'''' k s x y) = (term938 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413669 _106189 _106193 y k s) (@lem4413632 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4413680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413681 {_106189 _106193 : Type'} (f : type845 _106189 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413680 (_106193 -> Prop) (type734 _106189 _106193) f x). Qed.
Lemma lem4413682 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (@cartesian_product _106189 _106193 k) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k).
Proof. exact (@lem4413681 _106189 _106193 (@cartesian_product _106189 _106193) k). Qed.
Lemma lem4413683 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4413684 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s).
Proof. exact (MK_COMB (@lem4413682 _106189 _106193 k) (@lem4413683 _106189 _106193 s)). Qed.
Lemma lem4413686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413687 {_106189 _106193 : Type'} (f : type734 _106189 _106193) (x : type1470 _106189 _106193) : (f x) = (@I ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413686 (type1470 _106189 _106193) (type805 _106189 _106193) f x). Qed.
Lemma lem4413688 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s) = (term931 _106189 _106193 k s).
Proof. exact (@lem4413687 _106189 _106193 (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k) s). Qed.
Lemma lem4413690 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (TRANS (@lem4413684 _106189 _106193 k s) (@lem4413688 _106189 _106193 k s)). Qed.
Lemma lem4413691 {_106189 _106193 : Type'} (x : _106193 -> _106189) : (@IN (_106193 -> _106189) x) = (@IN (_106193 -> _106189) x).
Proof. exact (eq_refl (@IN (_106193 -> _106189) x)). Qed.
Lemma lem4413692 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 x k s) = (term932 _106189 _106193 x k s).
Proof. exact (MK_COMB (@lem4413691 _106189 _106193 x) (@lem4413690 _106189 _106193 k s)). Qed.
Lemma lem4413694 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413695 {_106189 _106193 : Type'} (f : type773 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413694 (_106193 -> _106189) (type207 _106189 _106193) f x). Qed.
Lemma lem4413696 {_106189 _106193 : Type'} (x : _106193 -> _106189) : (@IN (_106193 -> _106189) x) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) x).
Proof. exact (@lem4413695 _106189 _106193 (@IN (_106193 -> _106189)) x). Qed.
Lemma lem4413697 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term931 _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (eq_refl (term931 _106189 _106193 k s)). Qed.
Lemma lem4413698 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 x k s) = (term933 _106189 _106193 x k s).
Proof. exact (MK_COMB (@lem4413696 _106189 _106193 x) (@lem4413697 _106189 _106193 k s)). Qed.
Lemma lem4413700 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413701 {_106189 _106193 : Type'} (f : type207 _106189 _106193) (x : type805 _106189 _106193) : (f x) = (@I (((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413700 (type805 _106189 _106193) Prop f x). Qed.
Lemma lem4413702 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term933 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (@lem4413701 _106189 _106193 (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) x) (term931 _106189 _106193 k s)). Qed.
Lemma lem4413703 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (TRANS (@lem4413698 _106189 _106193 x k s) (@lem4413702 _106189 _106193 x k s)). Qed.
Lemma lem4413704 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (TRANS (@lem4413692 _106189 _106193 x k s) (@lem4413703 _106189 _106193 x k s)). Qed.
Lemma lem4413705 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term245 _106189 _106193 x k s) = (term935 _106189 _106193 x k s).
Proof. exact (MK_COMB (@lem4413671) (@lem4413704 _106189 _106193 x k s)). Qed.
Lemma lem4413706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4413707 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term221 _106189 _106193 x k s) = (term936 _106189 _106193 x k s).
Proof. exact (MK_COMB (@lem4413706) (@lem4413705 _106189 _106193 x k s)). Qed.
Lemma lem4413708 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term939 _106189 _106193 i'''' k s x y) = (term940 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413707 _106189 _106193 x k s) (@lem4413670 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4413710 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term941 _106189 _106193 i'''' k s x y) = (term942 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413709) (@lem4413708 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413711 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term943 _106189 _106193 i'''' k s x y) = (term944 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4413710 _106189 _106193 i'''' k s x y) (@lem4413489 _106189 _106193 x y)). Qed.
Lemma lem4413712 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (term945 _106189 _106193 i'''' k s x) = (term946 _106189 _106193 i'''' k s x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4413711 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4413713 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4413714 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (term947 _106189 _106193 i'''' k s x) = (term948 _106189 _106193 i'''' k s x).
Proof. exact (MK_COMB (@lem4413713 _106189 _106193) (@lem4413712 _106189 _106193 i'''' k s x)). Qed.
Lemma lem4413715 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term949 _106189 _106193 i'''' k s) = (term950 _106189 _106193 i'''' k s).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4413714 _106189 _106193 i'''' k s x)). Qed.
Lemma lem4413716 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4413717 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term951 _106189 _106193 i'''' k s) = (term952 _106189 _106193 i'''' k s).
Proof. exact (MK_COMB (@lem4413716 _106189 _106193) (@lem4413715 _106189 _106193 i'''' k s)). Qed.
Lemma lem4413718 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) : (term953 _106189 _106193 i'''' k) = (term954 _106189 _106193 i'''' k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4413717 _106189 _106193 i'''' k s)). Qed.
Lemma lem4413719 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4413720 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) : (term377 _106189 _106193 i'''' k) = (term955 _106189 _106193 i'''' k).
Proof. exact (MK_COMB (@lem4413719 _106189 _106193) (@lem4413718 _106189 _106193 i'''' k)). Qed.
Lemma lem4413721 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) : (term379 _106189 _106193 i'''') = (term956 _106189 _106193 i'''').
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4413720 _106189 _106193 i'''' k)). Qed.
Lemma lem4413722 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4413723 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) : (term381 _106189 _106193 i'''') = (term957 _106189 _106193 i'''').
Proof. exact (MK_COMB (@lem4413722 _106193) (@lem4413721 _106189 _106193 i'''')). Qed.
Lemma lem4413724 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term957 _106189 _106193 i''''.
Proof. exact (EQ_MP (@lem4413723 _106189 _106193 i'''') (@lem4412519 _106189 _106193 i'''' h1)). Qed.
Lemma lem4413725 {_106189 : Type'} : (@eq _106189) = (@eq _106189).
Proof. exact (eq_refl (@eq _106189)). Qed.
Lemma lem4413730 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413731 {_106189 _106193 : Type'} (f : _106193 -> _106189) (x : _106193) : (f x) = (@I (_106193 -> _106189) f x).
Proof. exact (@lem4413730 _106193 _106189 f x). Qed.
Lemma lem4413733 {_106189 _106193 : Type'} (x : _106193 -> _106189) (i : _106193) : (x i) = (@I (_106193 -> _106189) x i).
Proof. exact (@lem4413731 _106189 _106193 x i). Qed.
Lemma lem4413738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413739 {_106189 _106193 : Type'} (f : _106193 -> _106189) (x : _106193) : (f x) = (@I (_106193 -> _106189) f x).
Proof. exact (@lem4413738 _106193 _106189 f x). Qed.
Lemma lem4413741 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i : _106193) : (y i) = (@I (_106193 -> _106189) y i).
Proof. exact (@lem4413739 _106189 _106193 y i). Qed.
Lemma lem4413742 {_106189 _106193 : Type'} (x : _106193 -> _106189) (i : _106193) : (term958 _106189 _106193 x i) = (term959 _106189 _106193 x i).
Proof. exact (MK_COMB (@lem4413725 _106189) (@lem4413733 _106189 _106193 x i)). Qed.
Lemma lem4413743 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : ((x i) = (y i)) = ((@I (_106193 -> _106189) x i) = (@I (_106193 -> _106189) y i)).
Proof. exact (MK_COMB (@lem4413742 _106189 _106193 x i) (@lem4413741 _106189 _106193 y i)). Qed.
Lemma lem4413744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4413751 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413752 {_106193 : Type'} (f : type1364 _106193) (x : _106193) : (f x) = (@I (_106193 -> (_106193 -> Prop) -> Prop) f x).
Proof. exact (@lem4413751 _106193 (type686 _106193) f x). Qed.
Lemma lem4413753 {_106193 : Type'} (i : _106193) : (@IN _106193 i) = (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i).
Proof. exact (@lem4413752 _106193 (@IN _106193) i). Qed.
Lemma lem4413754 {_106193 : Type'} (k : _106193 -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4413755 {_106193 : Type'} (i : _106193) (k : _106193 -> Prop) : (@IN _106193 i k) = (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i k).
Proof. exact (MK_COMB (@lem4413753 _106193 i) (@lem4413754 _106193 k)). Qed.
Lemma lem4413757 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413758 {_106193 : Type'} (f : type686 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> Prop) f x).
Proof. exact (@lem4413757 (_106193 -> Prop) Prop f x). Qed.
Lemma lem4413759 {_106193 : Type'} (i : _106193) (k : _106193 -> Prop) : (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i k) = (term960 _106193 i k).
Proof. exact (@lem4413758 _106193 (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i) k). Qed.
Lemma lem4413761 {_106193 : Type'} (i : _106193) (k : _106193 -> Prop) : (@IN _106193 i k) = (term960 _106193 i k).
Proof. exact (TRANS (@lem4413755 _106193 i k) (@lem4413759 _106193 i k)). Qed.
Lemma lem4413762 {_106193 : Type'} (i : _106193) (k : _106193 -> Prop) : (term961 _106193 i k) = (term962 _106193 i k).
Proof. exact (MK_COMB (@lem4413744) (@lem4413761 _106193 i k)). Qed.
Lemma lem4413763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4413764 {_106193 : Type'} (i : _106193) (k : _106193 -> Prop) : (term963 _106193 i k) = (term964 _106193 i k).
Proof. exact (MK_COMB (@lem4413763) (@lem4413762 _106193 i k)). Qed.
Lemma lem4413765 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term106 _106189 _106193 k x y i) = (term965 _106189 _106193 k x y i).
Proof. exact (MK_COMB (@lem4413764 _106193 i k) (@lem4413743 _106189 _106193 x y i)). Qed.
Lemma lem4413766 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term116 _106189 _106193 k x y) = (term966 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4413765 _106189 _106193 k x y i)). Qed.
Lemma lem4413767 {_106193 : Type'} : (@all _106193) = (@all _106193).
Proof. exact (eq_refl (@all _106193)). Qed.
Lemma lem4413768 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term117 _106189 _106193 k x y) = (term967 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4413767 _106193) (@lem4413766 _106189 _106193 k x y)). Qed.
Lemma lem4413777 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term118 _106189 _106193 x y) = (term118 _106189 _106193 x y).
Proof. exact (eq_refl (term118 _106189 _106193 x y)). Qed.
Lemma lem4413778 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term120 _106189 _106193 k x y) = (term968 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4413777 _106189 _106193 x y) (@lem4413768 _106189 _106193 k x y)). Qed.
Lemma lem4413779 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4413780 {_106189 : Type'} : (@eq _106189) = (@eq _106189).
Proof. exact (eq_refl (@eq _106189)). Qed.
Lemma lem4413785 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413786 {_106189 _106193 : Type'} (f : _106193 -> _106189) (x : _106193) : (f x) = (@I (_106193 -> _106189) f x).
Proof. exact (@lem4413785 _106193 _106189 f x). Qed.
Lemma lem4413788 {_106189 _106193 : Type'} (x : _106193 -> _106189) (i''''' : _106193) : (x i''''') = (@I (_106193 -> _106189) x i''''').
Proof. exact (@lem4413786 _106189 _106193 x i'''''). Qed.
Lemma lem4413793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413794 {_106189 _106193 : Type'} (f : _106193 -> _106189) (x : _106193) : (f x) = (@I (_106193 -> _106189) f x).
Proof. exact (@lem4413793 _106193 _106189 f x). Qed.
Lemma lem4413796 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (y i''''') = (@I (_106193 -> _106189) y i''''').
Proof. exact (@lem4413794 _106189 _106193 y i'''''). Qed.
Lemma lem4413797 {_106189 _106193 : Type'} (x : _106193 -> _106189) (i''''' : _106193) : (term958 _106189 _106193 x i''''') = (term959 _106189 _106193 x i''''').
Proof. exact (MK_COMB (@lem4413780 _106189) (@lem4413788 _106189 _106193 x i''''')). Qed.
Lemma lem4413798 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : ((x i''''') = (y i''''')) = ((@I (_106193 -> _106189) x i''''') = (@I (_106193 -> _106189) y i''''')).
Proof. exact (MK_COMB (@lem4413797 _106189 _106193 x i''''') (@lem4413796 _106189 _106193 y i''''')). Qed.
Lemma lem4413799 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : (term969 _106189 _106193 x y i''''') = (term970 _106189 _106193 x y i''''').
Proof. exact (MK_COMB (@lem4413779) (@lem4413798 _106189 _106193 x y i''''')). Qed.
Lemma lem4413806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413807 {_106193 : Type'} (f : type1364 _106193) (x : _106193) : (f x) = (@I (_106193 -> (_106193 -> Prop) -> Prop) f x).
Proof. exact (@lem4413806 _106193 (type686 _106193) f x). Qed.
Lemma lem4413808 {_106193 : Type'} (i''''' : _106193) : (@IN _106193 i''''') = (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i''''').
Proof. exact (@lem4413807 _106193 (@IN _106193) i'''''). Qed.
Lemma lem4413809 {_106193 : Type'} (k : _106193 -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4413810 {_106193 : Type'} (i''''' : _106193) (k : _106193 -> Prop) : (@IN _106193 i''''' k) = (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i''''' k).
Proof. exact (MK_COMB (@lem4413808 _106193 i''''') (@lem4413809 _106193 k)). Qed.
Lemma lem4413812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413813 {_106193 : Type'} (f : type686 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> Prop) f x).
Proof. exact (@lem4413812 (_106193 -> Prop) Prop f x). Qed.
Lemma lem4413814 {_106193 : Type'} (i''''' : _106193) (k : _106193 -> Prop) : (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i''''' k) = (term960 _106193 i''''' k).
Proof. exact (@lem4413813 _106193 (@I (_106193 -> (_106193 -> Prop) -> Prop) (@IN _106193) i''''') k). Qed.
Lemma lem4413816 {_106193 : Type'} (i''''' : _106193) (k : _106193 -> Prop) : (@IN _106193 i''''' k) = (term960 _106193 i''''' k).
Proof. exact (TRANS (@lem4413810 _106193 i''''' k) (@lem4413814 _106193 i''''' k)). Qed.
Lemma lem4413817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4413818 {_106193 : Type'} (i''''' : _106193) (k : _106193 -> Prop) : (term971 _106193 i''''' k) = (term972 _106193 i''''' k).
Proof. exact (MK_COMB (@lem4413817) (@lem4413816 _106193 i''''' k)). Qed.
Lemma lem4413819 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : (term105 _106189 _106193 k x y i''''') = (term973 _106189 _106193 k x y i''''').
Proof. exact (MK_COMB (@lem4413818 _106193 i''''' k) (@lem4413799 _106189 _106193 x y i''''')). Qed.
Lemma lem4413826 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term121 _106189 _106193 x y) = (term121 _106189 _106193 x y).
Proof. exact (eq_refl (term121 _106189 _106193 x y)). Qed.
Lemma lem4413827 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : (term177 _106189 _106193 k x y i''''') = (term974 _106189 _106193 k x y i''''').
Proof. exact (MK_COMB (@lem4413826 _106189 _106193 x y) (@lem4413819 _106189 _106193 k x y i''''')). Qed.
Lemma lem4413828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4413829 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : (term194 _106189 _106193 k x y i''''') = (term975 _106189 _106193 k x y i''''').
Proof. exact (MK_COMB (@lem4413828) (@lem4413827 _106189 _106193 k x y i''''')). Qed.
Lemma lem4413830 {_106189 _106193 : Type'} (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term196 _106189 _106193 i''''' k x y) = (term976 _106189 _106193 i''''' k x y).
Proof. exact (MK_COMB (@lem4413829 _106189 _106193 k x y i''''') (@lem4413778 _106189 _106193 k x y)). Qed.
Lemma lem4413839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413840 {_106189 _106193 : Type'} (f : type845 _106189 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413839 (_106193 -> Prop) (type734 _106189 _106193) f x). Qed.
Lemma lem4413841 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (@cartesian_product _106189 _106193 k) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k).
Proof. exact (@lem4413840 _106189 _106193 (@cartesian_product _106189 _106193) k). Qed.
Lemma lem4413842 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4413843 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s).
Proof. exact (MK_COMB (@lem4413841 _106189 _106193 k) (@lem4413842 _106189 _106193 s)). Qed.
Lemma lem4413845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413846 {_106189 _106193 : Type'} (f : type734 _106189 _106193) (x : type1470 _106189 _106193) : (f x) = (@I ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413845 (type1470 _106189 _106193) (type805 _106189 _106193) f x). Qed.
Lemma lem4413847 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s) = (term931 _106189 _106193 k s).
Proof. exact (@lem4413846 _106189 _106193 (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k) s). Qed.
Lemma lem4413849 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (TRANS (@lem4413843 _106189 _106193 k s) (@lem4413847 _106189 _106193 k s)). Qed.
Lemma lem4413850 {_106189 _106193 : Type'} (y : _106193 -> _106189) : (@IN (_106193 -> _106189) y) = (@IN (_106193 -> _106189) y).
Proof. exact (eq_refl (@IN (_106193 -> _106189) y)). Qed.
Lemma lem4413851 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 y k s) = (term932 _106189 _106193 y k s).
Proof. exact (MK_COMB (@lem4413850 _106189 _106193 y) (@lem4413849 _106189 _106193 k s)). Qed.
Lemma lem4413853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413854 {_106189 _106193 : Type'} (f : type773 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413853 (_106193 -> _106189) (type207 _106189 _106193) f x). Qed.
Lemma lem4413855 {_106189 _106193 : Type'} (y : _106193 -> _106189) : (@IN (_106193 -> _106189) y) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) y).
Proof. exact (@lem4413854 _106189 _106193 (@IN (_106193 -> _106189)) y). Qed.
Lemma lem4413856 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term931 _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (eq_refl (term931 _106189 _106193 k s)). Qed.
Lemma lem4413857 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 y k s) = (term933 _106189 _106193 y k s).
Proof. exact (MK_COMB (@lem4413855 _106189 _106193 y) (@lem4413856 _106189 _106193 k s)). Qed.
Lemma lem4413859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413860 {_106189 _106193 : Type'} (f : type207 _106189 _106193) (x : type805 _106189 _106193) : (f x) = (@I (((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413859 (type805 _106189 _106193) Prop f x). Qed.
Lemma lem4413861 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term933 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (@lem4413860 _106189 _106193 (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) y) (term931 _106189 _106193 k s)). Qed.
Lemma lem4413862 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (TRANS (@lem4413857 _106189 _106193 y k s) (@lem4413861 _106189 _106193 y k s)). Qed.
Lemma lem4413863 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (TRANS (@lem4413851 _106189 _106193 y k s) (@lem4413862 _106189 _106193 y k s)). Qed.
Lemma lem4413872 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413873 {_106189 _106193 : Type'} (f : type845 _106189 _106193) (x : _106193 -> Prop) : (f x) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413872 (_106193 -> Prop) (type734 _106189 _106193) f x). Qed.
Lemma lem4413874 {_106189 _106193 : Type'} (k : _106193 -> Prop) : (@cartesian_product _106189 _106193 k) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k).
Proof. exact (@lem4413873 _106189 _106193 (@cartesian_product _106189 _106193) k). Qed.
Lemma lem4413875 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4413876 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s).
Proof. exact (MK_COMB (@lem4413874 _106189 _106193 k) (@lem4413875 _106189 _106193 s)). Qed.
Lemma lem4413878 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413879 {_106189 _106193 : Type'} (f : type734 _106189 _106193) (x : type1470 _106189 _106193) : (f x) = (@I ((_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) f x).
Proof. exact (@lem4413878 (type1470 _106189 _106193) (type805 _106189 _106193) f x). Qed.
Lemma lem4413880 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k s) = (term931 _106189 _106193 k s).
Proof. exact (@lem4413879 _106189 _106193 (@I ((_106193 -> Prop) -> (_106193 -> _106189 -> Prop) -> (_106193 -> _106189) -> Prop) (@cartesian_product _106189 _106193) k) s). Qed.
Lemma lem4413882 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (@cartesian_product _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (TRANS (@lem4413876 _106189 _106193 k s) (@lem4413880 _106189 _106193 k s)). Qed.
Lemma lem4413883 {_106189 _106193 : Type'} (x : _106193 -> _106189) : (@IN (_106193 -> _106189) x) = (@IN (_106193 -> _106189) x).
Proof. exact (eq_refl (@IN (_106193 -> _106189) x)). Qed.
Lemma lem4413884 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 x k s) = (term932 _106189 _106193 x k s).
Proof. exact (MK_COMB (@lem4413883 _106189 _106193 x) (@lem4413882 _106189 _106193 k s)). Qed.
Lemma lem4413886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413887 {_106189 _106193 : Type'} (f : type773 _106189 _106193) (x : _106193 -> _106189) : (f x) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413886 (_106193 -> _106189) (type207 _106189 _106193) f x). Qed.
Lemma lem4413888 {_106189 _106193 : Type'} (x : _106193 -> _106189) : (@IN (_106193 -> _106189) x) = (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) x).
Proof. exact (@lem4413887 _106189 _106193 (@IN (_106193 -> _106189)) x). Qed.
Lemma lem4413889 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term931 _106189 _106193 k s) = (term931 _106189 _106193 k s).
Proof. exact (eq_refl (term931 _106189 _106193 k s)). Qed.
Lemma lem4413890 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 x k s) = (term933 _106189 _106193 x k s).
Proof. exact (MK_COMB (@lem4413888 _106189 _106193 x) (@lem4413889 _106189 _106193 k s)). Qed.
Lemma lem4413892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4413893 {_106189 _106193 : Type'} (f : type207 _106189 _106193) (x : type805 _106189 _106193) : (f x) = (@I (((_106193 -> _106189) -> Prop) -> Prop) f x).
Proof. exact (@lem4413892 (type805 _106189 _106193) Prop f x). Qed.
Lemma lem4413894 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term933 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (@lem4413893 _106189 _106193 (@I ((_106193 -> _106189) -> ((_106193 -> _106189) -> Prop) -> Prop) (@IN (_106193 -> _106189)) x) (term931 _106189 _106193 k s)). Qed.
Lemma lem4413895 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term932 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (TRANS (@lem4413890 _106189 _106193 x k s) (@lem4413894 _106189 _106193 x k s)). Qed.
Lemma lem4413896 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term225 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (TRANS (@lem4413884 _106189 _106193 x k s) (@lem4413895 _106189 _106193 x k s)). Qed.
Lemma lem4413897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4413898 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term67 _106189 _106193 x k s) = (term977 _106189 _106193 x k s).
Proof. exact (MK_COMB (@lem4413897) (@lem4413896 _106189 _106193 x k s)). Qed.
Lemma lem4413899 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term133 _106189 _106193 x y k s) = (term978 _106189 _106193 x y k s).
Proof. exact (MK_COMB (@lem4413898 _106189 _106193 x k s) (@lem4413863 _106189 _106193 y k s)). Qed.
Lemma lem4413900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4413901 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term129 _106189 _106193 x y k s) = (term979 _106189 _106193 x y k s).
Proof. exact (MK_COMB (@lem4413900) (@lem4413899 _106189 _106193 x y k s)). Qed.
Lemma lem4413902 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term209 _106189 _106193 s i''''' k x y) = (term980 _106189 _106193 s i''''' k x y).
Proof. exact (MK_COMB (@lem4413901 _106189 _106193 x y k s) (@lem4413830 _106189 _106193 i''''' k x y)). Qed.
Lemma lem4413903 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term980 _106189 _106193 s i''''' k x y.
Proof. exact (EQ_MP (@lem4413902 _106189 _106193 s i''''' k x y) (@lem4412524 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4413904 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term976 _106189 _106193 i''''' k x y.
Proof. exact (proj2 (@lem4413903 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4413905 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term978 _106189 _106193 x y k s.
Proof. exact (proj1 (@lem4413903 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4413908 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : term974 _106189 _106193 k x y i'''''.
Proof. exact (h1). Qed.
Lemma lem4413909 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term968 _106189 _106193 k x y.
Proof. exact (h1). Qed.
Lemma lem4413910 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : term973 _106189 _106193 k x y i'''''.
Proof. exact (proj2 (@lem4413908 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4413914 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term967 _106189 _106193 k x y.
Proof. exact (proj2 (@lem4413909 _106189 _106193 k x y h1)). Qed.
Lemma lem4414441 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4414458 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term938 _106189 _106193 i'''' k s x y) = (term981 _106189 _106193 i'''' k s x y).
Proof. exact (@lem19490 (term926 _106189 _106193 i'''' s x y k) (term935 _106189 _106193 y k s) (term919 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4414461 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term936 _106189 _106193 x k s) = (term936 _106189 _106193 x k s).
Proof. exact (eq_refl (term936 _106189 _106193 x k s)). Qed.
Lemma lem4414462 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term940 _106189 _106193 i'''' k s x y) = (term982 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4414461 _106189 _106193 x k s) (@lem4414458 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4414469 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term982 _106189 _106193 i'''' k s x y) = (term983 _106189 _106193 i'''' k s x y).
Proof. exact (@lem19490 (term984 _106189 _106193 i'''' s x y k) (term935 _106189 _106193 x k s) (term985 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4414470 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term940 _106189 _106193 i'''' k s x y) = (term983 _106189 _106193 i'''' k s x y).
Proof. exact (TRANS (@lem4414462 _106189 _106193 i'''' k s x y) (@lem4414469 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4414471 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4414472 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term942 _106189 _106193 i'''' k s x y) = (term986 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4414471) (@lem4414470 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4414473 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term944 _106189 _106193 i'''' k s x y) = (term987 _106189 _106193 i'''' k s x y).
Proof. exact (MK_COMB (@lem4414472 _106189 _106193 i'''' k s x y) (@lem4414441 _106189 _106193 x y)). Qed.
Lemma lem4414480 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term987 _106189 _106193 i'''' k s x y) = (term988 _106189 _106193 i'''' k s x y).
Proof. exact (@lem19699 (term989 _106189 _106193 i'''' s x y k) (term990 _106189 _106193 i'''' k s x y) (x = y)). Qed.
Lemma lem4414481 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term944 _106189 _106193 i'''' k s x y) = (term988 _106189 _106193 i'''' k s x y).
Proof. exact (TRANS (@lem4414473 _106189 _106193 i'''' k s x y) (@lem4414480 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4414482 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (term946 _106189 _106193 i'''' k s x) = (term991 _106189 _106193 i'''' k s x).
Proof. exact (fun_ext (fun y : _106193 -> _106189 => @lem4414481 _106189 _106193 i'''' k s x y)). Qed.
Lemma lem4414483 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4414484 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) : (term948 _106189 _106193 i'''' k s x) = (term992 _106189 _106193 i'''' k s x).
Proof. exact (MK_COMB (@lem4414483 _106189 _106193) (@lem4414482 _106189 _106193 i'''' k s x)). Qed.
Lemma lem4414485 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term950 _106189 _106193 i'''' k s) = (term993 _106189 _106193 i'''' k s).
Proof. exact (fun_ext (fun x : _106193 -> _106189 => @lem4414484 _106189 _106193 i'''' k s x)). Qed.
Lemma lem4414486 {_106189 _106193 : Type'} : (@all (_106193 -> _106189)) = (@all (_106193 -> _106189)).
Proof. exact (eq_refl (@all (_106193 -> _106189))). Qed.
Lemma lem4414487 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term952 _106189 _106193 i'''' k s) = (term994 _106189 _106193 i'''' k s).
Proof. exact (MK_COMB (@lem4414486 _106189 _106193) (@lem4414485 _106189 _106193 i'''' k s)). Qed.
Lemma lem4414488 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) : (term954 _106189 _106193 i'''' k) = (term995 _106189 _106193 i'''' k).
Proof. exact (fun_ext (fun s : type1470 _106189 _106193 => @lem4414487 _106189 _106193 i'''' k s)). Qed.
Lemma lem4414489 {_106189 _106193 : Type'} : (@all (_106193 -> _106189 -> Prop)) = (@all (_106193 -> _106189 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> _106189 -> Prop))). Qed.
Lemma lem4414490 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) : (term955 _106189 _106193 i'''' k) = (term996 _106189 _106193 i'''' k).
Proof. exact (MK_COMB (@lem4414489 _106189 _106193) (@lem4414488 _106189 _106193 i'''' k)). Qed.
Lemma lem4414491 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) : (term956 _106189 _106193 i'''') = (term997 _106189 _106193 i'''').
Proof. exact (fun_ext (fun k : _106193 -> Prop => @lem4414490 _106189 _106193 i'''' k)). Qed.
Lemma lem4414492 {_106193 : Type'} : (@all (_106193 -> Prop)) = (@all (_106193 -> Prop)).
Proof. exact (eq_refl (@all (_106193 -> Prop))). Qed.
Lemma lem4414494 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) : (term957 _106189 _106193 i'''') = (term998 _106189 _106193 i'''').
Proof. exact (MK_COMB (@lem4414492 _106193) (@lem4414491 _106189 _106193 i'''')). Qed.
Lemma lem4414495 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term998 _106189 _106193 i''''.
Proof. exact (EQ_MP (@lem4414494 _106189 _106193 i'''') (@lem4413724 _106189 _106193 i'''' h1)). Qed.
Lemma lem4414515 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i : _106193) : (term965 _106189 _106193 k x y i) = (term965 _106189 _106193 k x y i).
Proof. exact (eq_refl (term965 _106189 _106193 k x y i)). Qed.
Lemma lem4414516 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term966 _106189 _106193 k x y) = (term966 _106189 _106193 k x y).
Proof. exact (fun_ext (fun i : _106193 => @lem4414515 _106189 _106193 k x y i)). Qed.
Lemma lem4414517 {_106193 : Type'} : (@all _106193) = (@all _106193).
Proof. exact (eq_refl (@all _106193)). Qed.
Lemma lem4414519 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term967 _106189 _106193 k x y) = (term967 _106189 _106193 k x y).
Proof. exact (MK_COMB (@lem4414517 _106193) (@lem4414516 _106189 _106193 k x y)). Qed.
Lemma lem4414520 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term967 _106189 _106193 k x y.
Proof. exact (EQ_MP (@lem4414519 _106189 _106193 k x y) (@lem4413914 _106189 _106193 k x y h1)). Qed.
Lemma lem4414629 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term999 _106189 _106193 i'''' _50489.
Proof. exact (@lem4414495 _106189 _106193 i'''' h1 _50489). Qed.
Lemma lem4414630 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) : (term999 _106189 _106193 i'''' _50489) = (term996 _106189 _106193 i'''' _50489).
Proof. exact (eq_refl (term999 _106189 _106193 i'''' _50489)). Qed.
Lemma lem4414631 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term996 _106189 _106193 i'''' _50489.
Proof. exact (EQ_MP (@lem4414630 _106189 _106193 i'''' _50489) (@lem4414629 _106189 _106193 _50489 i'''' h1)). Qed.
Lemma lem4414632 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1000 _106189 _106193 i'''' _50489 _50490.
Proof. exact (@lem4414631 _106189 _106193 _50489 i'''' h1 _50490). Qed.
Lemma lem4414633 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1000 _106189 _106193 i'''' _50489 _50490) = (term994 _106189 _106193 i'''' _50489 _50490).
Proof. exact (eq_refl (term1000 _106189 _106193 i'''' _50489 _50490)). Qed.
Lemma lem4414634 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term994 _106189 _106193 i'''' _50489 _50490.
Proof. exact (EQ_MP (@lem4414633 _106189 _106193 i'''' _50489 _50490) (@lem4414632 _106189 _106193 _50489 _50490 i'''' h1)). Qed.
Lemma lem4414635 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1001 _106189 _106193 i'''' _50489 _50490 _50491.
Proof. exact (@lem4414634 _106189 _106193 _50489 _50490 i'''' h1 _50491). Qed.
Lemma lem4414636 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) : (term1001 _106189 _106193 i'''' _50489 _50490 _50491) = (term992 _106189 _106193 i'''' _50489 _50490 _50491).
Proof. exact (eq_refl (term1001 _106189 _106193 i'''' _50489 _50490 _50491)). Qed.
Lemma lem4414637 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term992 _106189 _106193 i'''' _50489 _50490 _50491.
Proof. exact (EQ_MP (@lem4414636 _106189 _106193 i'''' _50489 _50490 _50491) (@lem4414635 _106189 _106193 _50489 _50490 _50491 i'''' h1)). Qed.
Lemma lem4414638 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1002 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (@lem4414637 _106189 _106193 _50489 _50490 _50491 i'''' h1 _50492). Qed.
Lemma lem4414639 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1002 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term988 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (eq_refl (term1002 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4414640 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term988 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (EQ_MP (@lem4414639 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4414638 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1)). Qed.
Lemma lem4414641 {_106189 _106193 : Type'} (_50493 : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term1003 _106189 _106193 k x y _50493.
Proof. exact (@lem4414520 _106189 _106193 k x y h1 _50493). Qed.
Lemma lem4414642 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) : (term1003 _106189 _106193 k x y _50493) = (term965 _106189 _106193 k x y _50493).
Proof. exact (eq_refl (term1003 _106189 _106193 k x y _50493)). Qed.
Lemma lem4414654 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1004 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (proj2 (@lem4414640 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1)). Qed.
Lemma lem4414655 {_106189 _106193 : Type'} (_50490 : type1470 _106189 _106193) (_50489 : _106193 -> Prop) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1005 _106189 _106193 i'''' _50490 _50489 _50491 _50492.
Proof. exact (proj1 (@lem4414640 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1)). Qed.
Lemma lem4414669 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : x = y.
Proof. exact (proj1 (@lem4413908 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4414673 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : term970 _106189 _106193 x y i'''''.
Proof. exact (proj2 (@lem4413910 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4414859 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term1006 _106189 _106193 x y.
Proof. exact (proj1 (@lem4413909 _106189 _106193 k x y h1)). Qed.
Lemma lem4414865 {_106189 _106193 : Type'} (_50493 : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term965 _106189 _106193 k x y _50493.
Proof. exact (EQ_MP (@lem4414642 _106189 _106193 k x y _50493) (@lem4414641 _106189 _106193 _50493 k x y h1)). Qed.
Lemma lem4414869 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50489 : _106193 -> Prop) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1005 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1007 _106189 _106193 i'''' _50490 _50489 _50491 _50492).
Proof. exact (@lem4409657 (term935 _106189 _106193 _50491 _50489 _50490) (term984 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (_50491 = _50492)). Qed.
Lemma lem4414876 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50489 : _106193 -> Prop) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1008 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1009 _106189 _106193 i'''' _50490 _50489 _50491 _50492).
Proof. exact (@lem4409657 (term935 _106189 _106193 _50492 _50489 _50490) (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (_50491 = _50492)). Qed.
Lemma lem4414877 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term936 _106189 _106193 _50491 _50489 _50490) = (term936 _106189 _106193 _50491 _50489 _50490).
Proof. exact (eq_refl (term936 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4414880 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50489 : _106193 -> Prop) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1007 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492).
Proof. exact (MK_COMB (@lem4414877 _106189 _106193 _50491 _50489 _50490) (@lem4414876 _106189 _106193 i'''' _50490 _50489 _50491 _50492)). Qed.
Lemma lem4414882 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50489 : _106193 -> Prop) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1005 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492).
Proof. exact (TRANS (@lem4414869 _106189 _106193 i'''' _50490 _50489 _50491 _50492) (@lem4414880 _106189 _106193 i'''' _50490 _50489 _50491 _50492)). Qed.
Lemma lem4414883 {_106189 _106193 : Type'} (_50490 : type1470 _106189 _106193) (_50489 : _106193 -> Prop) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492.
Proof. exact (EQ_MP (@lem4414882 _106189 _106193 i'''' _50490 _50489 _50491 _50492) (@lem4414655 _106189 _106193 _50490 _50489 _50491 _50492 i'''' h1)). Qed.
Lemma lem4414887 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1004 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1011 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (@lem4409657 (term935 _106189 _106193 _50491 _50489 _50490) (term985 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (_50491 = _50492)). Qed.
Lemma lem4414894 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1012 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1013 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (@lem4409657 (term935 _106189 _106193 _50492 _50489 _50490) (term919 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (_50491 = _50492)). Qed.
Lemma lem4414895 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term936 _106189 _106193 _50491 _50489 _50490) = (term936 _106189 _106193 _50491 _50489 _50490).
Proof. exact (eq_refl (term936 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4414898 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1011 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4414895 _106189 _106193 _50491 _50489 _50490) (@lem4414894 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4414900 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1004 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (TRANS (@lem4414887 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4414898 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4414901 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (EQ_MP (@lem4414900 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4414654 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1)). Qed.
Lemma lem4415101 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (term1015 _106189 _106193 y i''''') = (term1015 _106189 _106193 y i''''').
Proof. exact (eq_refl (term1015 _106189 _106193 y i''''')). Qed.
Lemma lem4415102 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : (term1016 _106189 _106193 y i''''' x) = (term1017 _106189 _106193 i''''' y).
Proof. exact (MK_COMB (@lem4415101 _106189 _106193 y i''''') (@lem4414669 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4415103 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (term1017 _106189 _106193 i''''' y) = (term1018 _106189 _106193 y i''''').
Proof. exact (eq_refl (term1017 _106189 _106193 i''''' y)). Qed.
Lemma lem4415104 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) (x : _106193 -> _106189) : (term1019 _106189 _106193 y i''''' x) = (term1019 _106189 _106193 y i''''' x).
Proof. exact (eq_refl (term1019 _106189 _106193 y i''''' x)). Qed.
Lemma lem4415105 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : ((term1016 _106189 _106193 y i''''' x) = (term1017 _106189 _106193 i''''' y)) = ((term1016 _106189 _106193 y i''''' x) = (term1018 _106189 _106193 y i''''')).
Proof. exact (MK_COMB (@lem4415104 _106189 _106193 y i''''' x) (@lem4415103 _106189 _106193 y i''''')). Qed.
Lemma lem4415106 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : (term1016 _106189 _106193 y i''''' x) = (term970 _106189 _106193 x y i''''').
Proof. exact (eq_refl (term1016 _106189 _106193 y i''''' x)). Qed.
Lemma lem4415107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4415108 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : (term1019 _106189 _106193 y i''''' x) = (term1020 _106189 _106193 x y i''''').
Proof. exact (MK_COMB (@lem4415107) (@lem4415106 _106189 _106193 x y i''''')). Qed.
Lemma lem4415109 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (term1018 _106189 _106193 y i''''') = (term1018 _106189 _106193 y i''''').
Proof. exact (eq_refl (term1018 _106189 _106193 y i''''')). Qed.
Lemma lem4415110 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : ((term1016 _106189 _106193 y i''''' x) = (term1018 _106189 _106193 y i''''')) = ((term970 _106189 _106193 x y i''''') = (term1018 _106189 _106193 y i''''')).
Proof. exact (MK_COMB (@lem4415108 _106189 _106193 x y i''''') (@lem4415109 _106189 _106193 y i''''')). Qed.
Lemma lem4415111 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) : ((term1016 _106189 _106193 y i''''' x) = (term1017 _106189 _106193 i''''' y)) = ((term970 _106189 _106193 x y i''''') = (term1018 _106189 _106193 y i''''')).
Proof. exact (TRANS (@lem4415105 _106189 _106193 x y i''''') (@lem4415110 _106189 _106193 x y i''''')). Qed.
Lemma lem4415112 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : (term970 _106189 _106193 x y i''''') = (term1018 _106189 _106193 y i''''').
Proof. exact (EQ_MP (@lem4415111 _106189 _106193 x y i''''') (@lem4415102 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4415113 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : term1018 _106189 _106193 y i'''''.
Proof. exact (EQ_MP (@lem4415112 _106189 _106193 k x y i''''' h1) (@lem4414673 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4416148 {_106189 : Type'} (x : _106189) : x = x.
Proof. exact (@lem21386 _106189 x). Qed.
Lemma lem4416149 {_106189 : Type'} (x : _106189) : x = x.
Proof. exact (@lem4416148 _106189 x). Qed.
Lemma lem4416150 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (@I (_106193 -> _106189) y i''''') = (@I (_106193 -> _106189) y i''''').
Proof. exact (@lem4416149 _106189 (@I (_106193 -> _106189) y i''''')). Qed.
Lemma lem4416151 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : term1021 _106189 _106193 y i'''''.
Proof. exact (fun h0 : term1018 _106189 _106193 y i''''' => @lem4416150 _106189 _106193 y i'''''). Qed.
Lemma lem4416153 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4416154 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (term1021 _106189 _106193 y i''''') = ((@I (_106193 -> _106189) y i''''') = (@I (_106193 -> _106189) y i''''')).
Proof. exact (@lem4416153 ((@I (_106193 -> _106189) y i''''') = (@I (_106193 -> _106189) y i'''''))). Qed.
Lemma lem4416155 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (@I (_106193 -> _106189) y i''''') = (@I (_106193 -> _106189) y i''''').
Proof. exact (EQ_MP (@lem4416154 _106189 _106193 y i''''') (@lem4416151 _106189 _106193 y i''''')). Qed.
Lemma lem4416158 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4416160 {_106189 _106193 : Type'} (y : _106193 -> _106189) (i''''' : _106193) : (term1018 _106189 _106193 y i''''') = (term1023 _106189 _106193 y i''''').
Proof. exact (@lem4416158 ((@I (_106193 -> _106189) y i''''') = (@I (_106193 -> _106189) y i'''''))). Qed.
Lemma lem4416163 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : term1023 _106189 _106193 y i'''''.
Proof. exact (EQ_MP (@lem4416160 _106189 _106193 y i''''') (@lem4415113 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4416166 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : False.
Proof. exact (@lem4416163 _106189 _106193 k x y i''''' h1 (@lem4416155 _106189 _106193 y i''''')). Qed.
Lemma lem4416167 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : term1024.
Proof. exact (fun h0 : ~ False => @lem4416166 _106189 _106193 k x y i''''' h1). Qed.
Lemma lem4416169 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4416170 : term1024 = False.
Proof. exact (@lem4416169 False). Qed.
Lemma lem4417066 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 x k s.
Proof. exact (proj1 (@lem4413905 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417067 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term1025 _106189 _106193 x k s.
Proof. exact (fun h0 : term935 _106189 _106193 x k s => @lem4417066 _106189 _106193 s i''''' k x y h1). Qed.
Lemma lem4417069 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417070 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term1025 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (@lem4417069 (term934 _106189 _106193 x k s)). Qed.
Lemma lem4417071 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 x k s.
Proof. exact (EQ_MP (@lem4417070 _106189 _106193 x k s) (@lem4417067 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417073 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 y k s.
Proof. exact (proj2 (@lem4413905 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417074 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term1025 _106189 _106193 y k s.
Proof. exact (fun h0 : term935 _106189 _106193 y k s => @lem4417073 _106189 _106193 s i''''' k x y h1). Qed.
Lemma lem4417076 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417077 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term1025 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (@lem4417076 (term934 _106189 _106193 y k s)). Qed.
Lemma lem4417078 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 y k s.
Proof. exact (EQ_MP (@lem4417077 _106189 _106193 y k s) (@lem4417074 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417080 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 x k s.
Proof. exact (proj1 (@lem4413905 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417081 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term1025 _106189 _106193 x k s.
Proof. exact (fun h0 : term935 _106189 _106193 x k s => @lem4417080 _106189 _106193 s i''''' k x y h1). Qed.
Lemma lem4417083 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417084 {_106189 _106193 : Type'} (x : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term1025 _106189 _106193 x k s) = (term934 _106189 _106193 x k s).
Proof. exact (@lem4417083 (term934 _106189 _106193 x k s)). Qed.
Lemma lem4417085 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 x k s.
Proof. exact (EQ_MP (@lem4417084 _106189 _106193 x k s) (@lem4417081 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417087 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 y k s.
Proof. exact (proj2 (@lem4413905 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417088 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term1025 _106189 _106193 y k s.
Proof. exact (fun h0 : term935 _106189 _106193 y k s => @lem4417087 _106189 _106193 s i''''' k x y h1). Qed.
Lemma lem4417090 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417091 {_106189 _106193 : Type'} (y : _106193 -> _106189) (k : _106193 -> Prop) (s : type1470 _106189 _106193) : (term1025 _106189 _106193 y k s) = (term934 _106189 _106193 y k s).
Proof. exact (@lem4417090 (term934 _106189 _106193 y k s)). Qed.
Lemma lem4417092 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term209 _106189 _106193 s i''''' k x y) : term934 _106189 _106193 y k s.
Proof. exact (EQ_MP (@lem4417091 _106189 _106193 y k s) (@lem4417088 _106189 _106193 s i''''' k x y h1)). Qed.
Lemma lem4417095 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term1006 _106189 _106193 x y) : term1006 _106189 _106193 x y.
Proof. exact (h1). Qed.
Lemma lem4417096 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term1006 _106189 _106193 x y) : term1026 _106189 _106193 x y.
Proof. exact (fun h0 : x = y => @lem4417095 _106189 _106193 x y h1). Qed.
Lemma lem4417098 (p : Prop) : (term1027 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4417099 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term1026 _106189 _106193 x y) = (term1006 _106189 _106193 x y).
Proof. exact (@lem4417098 (x = y)). Qed.
Lemma lem4417100 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term1006 _106189 _106193 x y) : term1006 _106189 _106193 x y.
Proof. exact (EQ_MP (@lem4417099 _106189 _106193 x y) (@lem4417096 _106189 _106193 x y h1)). Qed.
Lemma lem4417116 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417117 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1009 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1028 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (@lem4417116 (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (term935 _106189 _106193 _50492 _50489 _50490) (_50491 = _50492)). Qed.
Lemma lem4417131 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4417132 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1029 _106189 _106193 _50489 _50490 _50491 _50492) = (term1030 _106189 _106193 _50491 _50492 _50489 _50490).
Proof. exact (@lem4417131 (_50491 = _50492) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417140 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) : (term1031 _106189 _106193 i'''' _50490 _50491 _50492 _50489) = (term1031 _106189 _106193 i'''' _50490 _50491 _50492 _50489).
Proof. exact (eq_refl (term1031 _106189 _106193 i'''' _50490 _50491 _50492 _50489)). Qed.
Lemma lem4417141 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1028 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1032 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417140 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (@lem4417132 _106189 _106193 _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417145 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417146 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1032 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1033 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417145 (_50491 = _50492) (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417164 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1028 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1033 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417141 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417146 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417165 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1009 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1033 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417117 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417164 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417166 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term936 _106189 _106193 _50491 _50489 _50490) = (term936 _106189 _106193 _50491 _50489 _50490).
Proof. exact (eq_refl (term936 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417167 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1034 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417166 _106189 _106193 _50491 _50489 _50490) (@lem4417165 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417171 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417172 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1034 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1035 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417171 (_50491 = _50492) (term935 _106189 _106193 _50491 _50489 _50490) (term1036 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417188 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417189 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1037 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1038 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417188 (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (term935 _106189 _106193 _50491 _50489 _50490) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417205 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1039 _106189 _106193 _50491 _50492) = (term1039 _106189 _106193 _50491 _50492).
Proof. exact (eq_refl (term1039 _106189 _106193 _50491 _50492)). Qed.
Lemma lem4417206 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1035 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417205 _106189 _106193 _50491 _50492) (@lem4417189 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417217 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1034 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417172 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417206 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417218 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417167 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417217 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4417220 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1041 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1042 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417219) (@lem4417218 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417244 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4417245 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1029 _106189 _106193 _50489 _50490 _50491 _50492) = (term1030 _106189 _106193 _50491 _50492 _50489 _50490).
Proof. exact (@lem4417244 (_50491 = _50492) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417253 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term936 _106189 _106193 _50491 _50489 _50490) = (term936 _106189 _106193 _50491 _50489 _50490).
Proof. exact (eq_refl (term936 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417254 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1043 _106189 _106193 _50489 _50490 _50491 _50492) = (term1044 _106189 _106193 _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417253 _106189 _106193 _50491 _50489 _50490) (@lem4417245 _106189 _106193 _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417258 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417259 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1044 _106189 _106193 _50491 _50492 _50489 _50490) = (term1045 _106189 _106193 _50491 _50492 _50489 _50490).
Proof. exact (@lem4417258 (_50491 = _50492) (term935 _106189 _106193 _50491 _50489 _50490) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417277 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1043 _106189 _106193 _50489 _50490 _50491 _50492) = (term1045 _106189 _106193 _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417254 _106189 _106193 _50491 _50492 _50489 _50490) (@lem4417259 _106189 _106193 _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417278 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) : (term1031 _106189 _106193 i'''' _50490 _50491 _50492 _50489) = (term1031 _106189 _106193 i'''' _50490 _50491 _50492 _50489).
Proof. exact (eq_refl (term1031 _106189 _106193 i'''' _50490 _50491 _50492 _50489)). Qed.
Lemma lem4417279 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1047 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417278 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (@lem4417277 _106189 _106193 _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417283 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417284 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1047 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417283 (_50491 = _50492) (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (term1048 _106189 _106193 _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417312 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417279 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417284 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417313 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : ((term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492)) = ((term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490)).
Proof. exact (MK_COMB (@lem4417220 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417312 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417315 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4417316 (x : Prop) : (x = x) = True.
Proof. exact (@lem4417315 Prop x). Qed.
Lemma lem4417317 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : ((term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490)) = True.
Proof. exact (@lem4417316 (term1040 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417318 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : ((term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492)) = True.
Proof. exact (TRANS (@lem4417313 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417317 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417319 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : True = ((term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492)).
Proof. exact (SYM (@lem4417318 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417320 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1010 _106189 _106193 i'''' _50490 _50489 _50491 _50492) = (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (EQ_MP (@lem4417319 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem0)). Qed.
Lemma lem4417321 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (EQ_MP (@lem4417320 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4414883 _106189 _106193 _50490 _50489 _50491 _50492 i'''' h1)). Qed.
Lemma lem4417323 (b : Prop) (a : Prop) : (a \/ b) = (term1049 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4417324 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) : (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1050 _106189 _106193 i'''' _50490 _50491 _50492 _50489).
Proof. exact (@lem4417323 (term1043 _106189 _106193 _50489 _50490 _50491 _50492) (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489)). Qed.
Lemma lem4417326 (a : Prop) (b : Prop) : (term1051 a b) = (term1052 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4417327 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1053 _106189 _106193 _50489 _50490 _50491 _50492) = (term1054 _106189 _106193 _50489 _50490 _50491 _50492).
Proof. exact (@lem4417326 (term935 _106189 _106193 _50491 _50489 _50490) (term1029 _106189 _106193 _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417329 (a : Prop) : (term1055 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4417330 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1056 _106189 _106193 _50491 _50489 _50490) = (term934 _106189 _106193 _50491 _50489 _50490).
Proof. exact (@lem4417329 (term934 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4417332 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1057 _106189 _106193 _50491 _50489 _50490) = (term977 _106189 _106193 _50491 _50489 _50490).
Proof. exact (MK_COMB (@lem4417331) (@lem4417330 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417334 (a : Prop) (b : Prop) : (term1051 a b) = (term1052 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4417335 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1058 _106189 _106193 _50489 _50490 _50491 _50492) = (term1059 _106189 _106193 _50489 _50490 _50491 _50492).
Proof. exact (@lem4417334 (term935 _106189 _106193 _50492 _50489 _50490) (_50491 = _50492)). Qed.
Lemma lem4417337 (a : Prop) : (term1055 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4417338 {_106189 _106193 : Type'} (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1056 _106189 _106193 _50492 _50489 _50490) = (term934 _106189 _106193 _50492 _50489 _50490).
Proof. exact (@lem4417337 (term934 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4417340 {_106189 _106193 : Type'} (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1057 _106189 _106193 _50492 _50489 _50490) = (term977 _106189 _106193 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417339) (@lem4417338 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417341 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1006 _106189 _106193 _50491 _50492) = (term1006 _106189 _106193 _50491 _50492).
Proof. exact (eq_refl (term1006 _106189 _106193 _50491 _50492)). Qed.
Lemma lem4417342 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1059 _106189 _106193 _50489 _50490 _50491 _50492) = (term1060 _106189 _106193 _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4417340 _106189 _106193 _50492 _50489 _50490) (@lem4417341 _106189 _106193 _50491 _50492)). Qed.
Lemma lem4417343 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1058 _106189 _106193 _50489 _50490 _50491 _50492) = (term1060 _106189 _106193 _50489 _50490 _50491 _50492).
Proof. exact (TRANS (@lem4417335 _106189 _106193 _50489 _50490 _50491 _50492) (@lem4417342 _106189 _106193 _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417344 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1054 _106189 _106193 _50489 _50490 _50491 _50492) = (term1061 _106189 _106193 _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4417332 _106189 _106193 _50491 _50489 _50490) (@lem4417343 _106189 _106193 _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417345 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1053 _106189 _106193 _50489 _50490 _50491 _50492) = (term1061 _106189 _106193 _50489 _50490 _50491 _50492).
Proof. exact (TRANS (@lem4417327 _106189 _106193 _50489 _50490 _50491 _50492) (@lem4417344 _106189 _106193 _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417346 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4417347 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1062 _106189 _106193 _50489 _50490 _50491 _50492) = (term1063 _106189 _106193 _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4417346) (@lem4417345 _106189 _106193 _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417348 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) : (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489) = (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489).
Proof. exact (eq_refl (term926 _106189 _106193 i'''' _50490 _50491 _50492 _50489)). Qed.
Lemma lem4417349 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) : (term1050 _106189 _106193 i'''' _50490 _50491 _50492 _50489) = (term1064 _106189 _106193 i'''' _50490 _50491 _50492 _50489).
Proof. exact (MK_COMB (@lem4417347 _106189 _106193 _50489 _50490 _50491 _50492) (@lem4417348 _106189 _106193 i'''' _50490 _50491 _50492 _50489)). Qed.
Lemma lem4417350 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) : (term1046 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1064 _106189 _106193 i'''' _50490 _50491 _50492 _50489).
Proof. exact (TRANS (@lem4417324 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (@lem4417349 _106189 _106193 i'''' _50490 _50491 _50492 _50489)). Qed.
Lemma lem4417352 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term1006 _106189 _106193 x y) (h2 : term209 _106189 _106193 s i''''' k x y) : term1060 _106189 _106193 k s x y.
Proof. exact (conj (@lem4417092 _106189 _106193 s i''''' k x y h2) (@lem4417100 _106189 _106193 x y h1)). Qed.
Lemma lem4417353 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term1006 _106189 _106193 x y) (h2 : term209 _106189 _106193 s i''''' k x y) : term1061 _106189 _106193 k s x y.
Proof. exact (conj (@lem4417085 _106189 _106193 s i''''' k x y h2) (@lem4417352 _106189 _106193 s i''''' k x y h1 h2)). Qed.
Lemma lem4417355 {_106189 _106193 : Type'} (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1064 _106189 _106193 i'''' _50490 _50491 _50492 _50489.
Proof. exact (EQ_MP (@lem4417350 _106189 _106193 i'''' _50490 _50491 _50492 _50489) (@lem4417321 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1)). Qed.
Lemma lem4417356 {_106189 _106193 : Type'} (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1064 _106189 _106193 i'''' _50490 _50491 _50492 _50489.
Proof. exact (@lem4417355 _106189 _106193 _50490 _50491 _50492 _50489 i'''' h1). Qed.
Lemma lem4417357 {_106189 _106193 : Type'} (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1064 _106189 _106193 i'''' s x y k.
Proof. exact (@lem4417356 _106189 _106193 s x y k i'''' h1). Qed.
Lemma lem4417360 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term209 _106189 _106193 s i''''' k x y) : term926 _106189 _106193 i'''' s x y k.
Proof. exact (@lem4417357 _106189 _106193 s x y k i'''' h1 (@lem4417353 _106189 _106193 s i''''' k x y h2 h3)). Qed.
Lemma lem4417361 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term209 _106189 _106193 s i''''' k x y) : term1065 _106189 _106193 i'''' s x y k.
Proof. exact (fun h0 : term1066 _106189 _106193 i'''' s x y k => @lem4417360 _106189 _106193 i'''' s i''''' k x y h1 h2 h3). Qed.
Lemma lem4417363 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417364 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (k : _106193 -> Prop) : (term1065 _106189 _106193 i'''' s x y k) = (term926 _106189 _106193 i'''' s x y k).
Proof. exact (@lem4417363 (term926 _106189 _106193 i'''' s x y k)). Qed.
Lemma lem4417365 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term209 _106189 _106193 s i''''' k x y) : term926 _106189 _106193 i'''' s x y k.
Proof. exact (EQ_MP (@lem4417364 _106189 _106193 i'''' s x y k) (@lem4417361 _106189 _106193 i'''' s i''''' k x y h1 h2 h3)). Qed.
Lemma lem4417371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4417372 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : (term965 _106189 _106193 k x y _50493) = (term1067 _106189 _106193 x y _50493 k).
Proof. exact (@lem4417371 ((@I (_106193 -> _106189) x _50493) = (@I (_106193 -> _106189) y _50493)) (term962 _106193 _50493 k)). Qed.
Lemma lem4417380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4417381 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : (term1068 _106189 _106193 k x y _50493) = (term1069 _106189 _106193 x y _50493 k).
Proof. exact (MK_COMB (@lem4417380) (@lem4417372 _106189 _106193 x y _50493 k)). Qed.
Lemma lem4417389 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : (term1067 _106189 _106193 x y _50493 k) = (term1067 _106189 _106193 x y _50493 k).
Proof. exact (eq_refl (term1067 _106189 _106193 x y _50493 k)). Qed.
Lemma lem4417390 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : ((term965 _106189 _106193 k x y _50493) = (term1067 _106189 _106193 x y _50493 k)) = ((term1067 _106189 _106193 x y _50493 k) = (term1067 _106189 _106193 x y _50493 k)).
Proof. exact (MK_COMB (@lem4417381 _106189 _106193 x y _50493 k) (@lem4417389 _106189 _106193 x y _50493 k)). Qed.
Lemma lem4417392 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4417393 (x : Prop) : (x = x) = True.
Proof. exact (@lem4417392 Prop x). Qed.
Lemma lem4417394 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : ((term1067 _106189 _106193 x y _50493 k) = (term1067 _106189 _106193 x y _50493 k)) = True.
Proof. exact (@lem4417393 (term1067 _106189 _106193 x y _50493 k)). Qed.
Lemma lem4417395 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : ((term965 _106189 _106193 k x y _50493) = (term1067 _106189 _106193 x y _50493 k)) = True.
Proof. exact (TRANS (@lem4417390 _106189 _106193 x y _50493 k) (@lem4417394 _106189 _106193 x y _50493 k)). Qed.
Lemma lem4417396 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : True = ((term965 _106189 _106193 k x y _50493) = (term1067 _106189 _106193 x y _50493 k)).
Proof. exact (SYM (@lem4417395 _106189 _106193 x y _50493 k)). Qed.
Lemma lem4417397 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) (k : _106193 -> Prop) : (term965 _106189 _106193 k x y _50493) = (term1067 _106189 _106193 x y _50493 k).
Proof. exact (EQ_MP (@lem4417396 _106189 _106193 x y _50493 k) (@lem0)). Qed.
Lemma lem4417398 {_106189 _106193 : Type'} (_50493 : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term1067 _106189 _106193 x y _50493 k.
Proof. exact (EQ_MP (@lem4417397 _106189 _106193 x y _50493 k) (@lem4414865 _106189 _106193 _50493 k x y h1)). Qed.
Lemma lem4417400 (b : Prop) (a : Prop) : (a \/ b) = (term1049 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4417401 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) : (term1067 _106189 _106193 x y _50493 k) = (term1070 _106189 _106193 k x y _50493).
Proof. exact (@lem4417400 (term962 _106193 _50493 k) ((@I (_106193 -> _106189) x _50493) = (@I (_106193 -> _106189) y _50493))). Qed.
Lemma lem4417403 (a : Prop) : (term1055 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4417404 {_106193 : Type'} (_50493 : _106193) (k : _106193 -> Prop) : (term1071 _106193 _50493 k) = (term960 _106193 _50493 k).
Proof. exact (@lem4417403 (term960 _106193 _50493 k)). Qed.
Lemma lem4417405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4417406 {_106193 : Type'} (_50493 : _106193) (k : _106193 -> Prop) : (term1072 _106193 _50493 k) = (term1073 _106193 _50493 k).
Proof. exact (MK_COMB (@lem4417405) (@lem4417404 _106193 _50493 k)). Qed.
Lemma lem4417407 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) : ((@I (_106193 -> _106189) x _50493) = (@I (_106193 -> _106189) y _50493)) = ((@I (_106193 -> _106189) x _50493) = (@I (_106193 -> _106189) y _50493)).
Proof. exact (eq_refl ((@I (_106193 -> _106189) x _50493) = (@I (_106193 -> _106189) y _50493))). Qed.
Lemma lem4417408 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) : (term1070 _106189 _106193 k x y _50493) = (term1074 _106189 _106193 k x y _50493).
Proof. exact (MK_COMB (@lem4417406 _106193 _50493 k) (@lem4417407 _106189 _106193 x y _50493)). Qed.
Lemma lem4417409 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (_50493 : _106193) : (term1067 _106189 _106193 x y _50493 k) = (term1074 _106189 _106193 k x y _50493).
Proof. exact (TRANS (@lem4417401 _106189 _106193 k x y _50493) (@lem4417408 _106189 _106193 k x y _50493)). Qed.
Lemma lem4417412 {_106189 _106193 : Type'} (_50493 : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term1074 _106189 _106193 k x y _50493.
Proof. exact (EQ_MP (@lem4417409 _106189 _106193 k x y _50493) (@lem4417398 _106189 _106193 _50493 k x y h1)). Qed.
Lemma lem4417413 {_106189 _106193 : Type'} (_50493 : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term1074 _106189 _106193 k x y _50493.
Proof. exact (@lem4417412 _106189 _106193 _50493 k x y h1). Qed.
Lemma lem4417414 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term1075 _106189 _106193 i'''' k s x y.
Proof. exact (@lem4417413 _106189 _106193 (term909 _106189 _106193 i'''' k s x y) k x y h1). Qed.
Lemma lem4417417 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term968 _106189 _106193 k x y) (h4 : term209 _106189 _106193 s i''''' k x y) : (term912 _106189 _106193 i'''' k s x y) = (term915 _106189 _106193 i'''' k s x y).
Proof. exact (@lem4417414 _106189 _106193 i'''' s k x y h3 (@lem4417365 _106189 _106193 i'''' s i''''' k x y h1 h2 h4)). Qed.
Lemma lem4417418 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term968 _106189 _106193 k x y) (h4 : term209 _106189 _106193 s i''''' k x y) : term1076 _106189 _106193 i'''' k s x y.
Proof. exact (fun h0 : term919 _106189 _106193 i'''' k s x y => @lem4417417 _106189 _106193 i'''' s i''''' k x y h1 h2 h3 h4). Qed.
Lemma lem4417420 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417421 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) : (term1076 _106189 _106193 i'''' k s x y) = ((term912 _106189 _106193 i'''' k s x y) = (term915 _106189 _106193 i'''' k s x y)).
Proof. exact (@lem4417420 ((term912 _106189 _106193 i'''' k s x y) = (term915 _106189 _106193 i'''' k s x y))). Qed.
Lemma lem4417422 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term968 _106189 _106193 k x y) (h4 : term209 _106189 _106193 s i''''' k x y) : (term912 _106189 _106193 i'''' k s x y) = (term915 _106189 _106193 i'''' k s x y).
Proof. exact (EQ_MP (@lem4417421 _106189 _106193 i'''' k s x y) (@lem4417418 _106189 _106193 i'''' s i''''' k x y h1 h2 h3 h4)). Qed.
Lemma lem4417438 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417439 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1013 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1077 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (@lem4417438 (term919 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (term935 _106189 _106193 _50492 _50489 _50490) (_50491 = _50492)). Qed.
Lemma lem4417455 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4417456 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1029 _106189 _106193 _50489 _50490 _50491 _50492) = (term1030 _106189 _106193 _50491 _50492 _50489 _50490).
Proof. exact (@lem4417455 (_50491 = _50492) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417464 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1078 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1078 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (eq_refl (term1078 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417465 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1077 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1079 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417464 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417456 _106189 _106193 _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417469 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417470 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1079 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1080 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417469 (_50491 = _50492) (term919 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417490 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1077 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1080 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417465 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417470 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417491 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1013 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1080 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417439 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417490 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417492 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term936 _106189 _106193 _50491 _50489 _50490) = (term936 _106189 _106193 _50491 _50489 _50490).
Proof. exact (eq_refl (term936 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417493 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1081 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417492 _106189 _106193 _50491 _50489 _50490) (@lem4417491 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417497 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417498 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1081 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1082 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417497 (_50491 = _50492) (term935 _106189 _106193 _50491 _50489 _50490) (term1083 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417514 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417515 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1084 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1085 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417514 (term919 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (term935 _106189 _106193 _50491 _50489 _50490) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417533 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1039 _106189 _106193 _50491 _50492) = (term1039 _106189 _106193 _50491 _50492).
Proof. exact (eq_refl (term1039 _106189 _106193 _50491 _50492)). Qed.
Lemma lem4417534 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1082 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417533 _106189 _106193 _50491 _50492) (@lem4417515 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417545 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1081 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417498 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417534 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417546 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417493 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417545 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417547 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4417548 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1087 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1088 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417547) (@lem4417546 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417574 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4417575 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term985 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1083 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417574 (term919 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417583 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term936 _106189 _106193 _50491 _50489 _50490) = (term936 _106189 _106193 _50491 _50489 _50490).
Proof. exact (eq_refl (term936 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417584 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term990 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1084 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417583 _106189 _106193 _50491 _50489 _50490) (@lem4417575 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417588 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4417589 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1084 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1085 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (@lem4417588 (term919 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (term935 _106189 _106193 _50491 _50489 _50490) (term935 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417607 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term990 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1085 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (TRANS (@lem4417584 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417589 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417608 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1039 _106189 _106193 _50491 _50492) = (term1039 _106189 _106193 _50491 _50492).
Proof. exact (eq_refl (term1039 _106189 _106193 _50491 _50492)). Qed.
Lemma lem4417609 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417608 _106189 _106193 _50491 _50492) (@lem4417607 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417620 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : ((term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492)) = ((term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490)).
Proof. exact (MK_COMB (@lem4417548 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417609 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4417623 (x : Prop) : (x = x) = True.
Proof. exact (@lem4417622 Prop x). Qed.
Lemma lem4417624 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : ((term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490) = (term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490)) = True.
Proof. exact (@lem4417623 (term1086 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417625 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : ((term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492)) = True.
Proof. exact (TRANS (@lem4417620 _106189 _106193 i'''' _50491 _50492 _50489 _50490) (@lem4417624 _106189 _106193 i'''' _50491 _50492 _50489 _50490)). Qed.
Lemma lem4417626 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : True = ((term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492)).
Proof. exact (SYM (@lem4417625 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417627 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1014 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (EQ_MP (@lem4417626 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem0)). Qed.
Lemma lem4417628 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (EQ_MP (@lem4417627 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4414901 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1)). Qed.
Lemma lem4417630 (b : Prop) (a : Prop) : (a \/ b) = (term1049 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4417631 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1090 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (@lem4417630 (term990 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (_50491 = _50492)). Qed.
Lemma lem4417633 (a : Prop) (b : Prop) : (term1051 a b) = (term1052 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4417634 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1091 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1092 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (@lem4417633 (term935 _106189 _106193 _50491 _50489 _50490) (term985 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417636 (a : Prop) : (term1055 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4417637 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1056 _106189 _106193 _50491 _50489 _50490) = (term934 _106189 _106193 _50491 _50489 _50490).
Proof. exact (@lem4417636 (term934 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4417639 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1057 _106189 _106193 _50491 _50489 _50490) = (term977 _106189 _106193 _50491 _50489 _50490).
Proof. exact (MK_COMB (@lem4417638) (@lem4417637 _106189 _106193 _50491 _50489 _50490)). Qed.
Lemma lem4417641 (a : Prop) (b : Prop) : (term1051 a b) = (term1052 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4417642 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1093 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1094 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (@lem4417641 (term935 _106189 _106193 _50492 _50489 _50490) (term919 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417644 (a : Prop) : (term1055 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4417645 {_106189 _106193 : Type'} (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1056 _106189 _106193 _50492 _50489 _50490) = (term934 _106189 _106193 _50492 _50489 _50490).
Proof. exact (@lem4417644 (term934 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4417647 {_106189 _106193 : Type'} (_50492 : _106193 -> _106189) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) : (term1057 _106189 _106193 _50492 _50489 _50490) = (term977 _106189 _106193 _50492 _50489 _50490).
Proof. exact (MK_COMB (@lem4417646) (@lem4417645 _106189 _106193 _50492 _50489 _50490)). Qed.
Lemma lem4417649 (a : Prop) : (term1055 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4417650 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1095 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = ((term912 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term915 _106189 _106193 i'''' _50489 _50490 _50491 _50492)).
Proof. exact (@lem4417649 ((term912 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term915 _106189 _106193 i'''' _50489 _50490 _50491 _50492))). Qed.
Lemma lem4417651 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1094 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1096 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4417647 _106189 _106193 _50492 _50489 _50490) (@lem4417650 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417652 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1093 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1096 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (TRANS (@lem4417642 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417651 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417653 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1092 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1097 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4417639 _106189 _106193 _50491 _50489 _50490) (@lem4417652 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417654 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1091 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1097 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (TRANS (@lem4417634 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417653 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417655 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4417656 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1098 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1099 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4417655) (@lem4417654 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417657 {_106189 _106193 : Type'} (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (_50491 = _50492) = (_50491 = _50492).
Proof. exact (eq_refl (_50491 = _50492)). Qed.
Lemma lem4417658 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1090 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1100 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (MK_COMB (@lem4417656 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417657 _106189 _106193 _50491 _50492)). Qed.
Lemma lem4417659 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) : (term1089 _106189 _106193 i'''' _50489 _50490 _50491 _50492) = (term1100 _106189 _106193 i'''' _50489 _50490 _50491 _50492).
Proof. exact (TRANS (@lem4417631 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417658 _106189 _106193 i'''' _50489 _50490 _50491 _50492)). Qed.
Lemma lem4417661 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term968 _106189 _106193 k x y) (h4 : term209 _106189 _106193 s i''''' k x y) : term1096 _106189 _106193 i'''' k s x y.
Proof. exact (conj (@lem4417078 _106189 _106193 s i''''' k x y h4) (@lem4417422 _106189 _106193 i'''' s i''''' k x y h1 h2 h3 h4)). Qed.
Lemma lem4417662 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term968 _106189 _106193 k x y) (h4 : term209 _106189 _106193 s i''''' k x y) : term1097 _106189 _106193 i'''' k s x y.
Proof. exact (conj (@lem4417071 _106189 _106193 s i''''' k x y h4) (@lem4417661 _106189 _106193 i'''' s i''''' k x y h1 h2 h3 h4)). Qed.
Lemma lem4417664 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1100 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (EQ_MP (@lem4417659 _106189 _106193 i'''' _50489 _50490 _50491 _50492) (@lem4417628 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1)). Qed.
Lemma lem4417665 {_106189 _106193 : Type'} (_50489 : _106193 -> Prop) (_50490 : type1470 _106189 _106193) (_50491 : _106193 -> _106189) (_50492 : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1100 _106189 _106193 i'''' _50489 _50490 _50491 _50492.
Proof. exact (@lem4417664 _106189 _106193 _50489 _50490 _50491 _50492 i'''' h1). Qed.
Lemma lem4417666 {_106189 _106193 : Type'} (k : _106193 -> Prop) (s : type1470 _106189 _106193) (x : _106193 -> _106189) (y : _106193 -> _106189) (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') : term1100 _106189 _106193 i'''' k s x y.
Proof. exact (@lem4417665 _106189 _106193 k s x y i'''' h1). Qed.
Lemma lem4417669 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term1006 _106189 _106193 x y) (h3 : term968 _106189 _106193 k x y) (h4 : term209 _106189 _106193 s i''''' k x y) : x = y.
Proof. exact (@lem4417666 _106189 _106193 k s x y i'''' h1 (@lem4417662 _106189 _106193 i'''' s i''''' k x y h1 h2 h3 h4)). Qed.
Lemma lem4417670 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term968 _106189 _106193 k x y) (h3 : term209 _106189 _106193 s i''''' k x y) : term1101 _106189 _106193 x y.
Proof. exact (fun h0 : term1006 _106189 _106193 x y => @lem4417669 _106189 _106193 i'''' s i''''' k x y h1 h0 h2 h3). Qed.
Lemma lem4417672 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417673 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term1101 _106189 _106193 x y) = (x = y).
Proof. exact (@lem4417672 (x = y)). Qed.
Lemma lem4417674 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term968 _106189 _106193 k x y) (h3 : term209 _106189 _106193 s i''''' k x y) : x = y.
Proof. exact (EQ_MP (@lem4417673 _106189 _106193 x y) (@lem4417670 _106189 _106193 i'''' s i''''' k x y h1 h2 h3)). Qed.
Lemma lem4417677 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4417679 {_106189 _106193 : Type'} (x : _106193 -> _106189) (y : _106193 -> _106189) : (term1006 _106189 _106193 x y) = (term1102 _106189 _106193 x y).
Proof. exact (@lem4417677 (x = y)). Qed.
Lemma lem4417682 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term968 _106189 _106193 k x y) : term1102 _106189 _106193 x y.
Proof. exact (EQ_MP (@lem4417679 _106189 _106193 x y) (@lem4414859 _106189 _106193 k x y h1)). Qed.
Lemma lem4417685 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term968 _106189 _106193 k x y) (h3 : term209 _106189 _106193 s i''''' k x y) : False.
Proof. exact (@lem4417682 _106189 _106193 k x y h2 (@lem4417674 _106189 _106193 i'''' s i''''' k x y h1 h2 h3)). Qed.
Lemma lem4417686 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term968 _106189 _106193 k x y) (h3 : term209 _106189 _106193 s i''''' k x y) : term1024.
Proof. exact (fun h0 : ~ False => @lem4417685 _106189 _106193 i'''' s i''''' k x y h1 h2 h3). Qed.
Lemma lem4417688 (p : Prop) : (term1022 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4417689 : term1024 = False.
Proof. exact (@lem4417688 False). Qed.
Lemma lem4417690 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term968 _106189 _106193 k x y) (h3 : term209 _106189 _106193 s i''''' k x y) : False.
Proof. exact (EQ_MP (@lem4417689) (@lem4417686 _106189 _106193 i'''' s i''''' k x y h1 h2 h3)). Qed.
Lemma lem4417691 {_106189 _106193 : Type'} (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (i''''' : _106193) (h1 : term974 _106189 _106193 k x y i''''') : False.
Proof. exact (EQ_MP (@lem4416170) (@lem4416167 _106189 _106193 k x y i''''' h1)). Qed.
Lemma lem4417692 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (i''''' : _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term209 _106189 _106193 s i''''' k x y) : False.
Proof. exact (or_elim (@lem4413904 _106189 _106193 s i''''' k x y h2) (fun h0 : term974 _106189 _106193 k x y i''''' => @lem4417691 _106189 _106193 k x y i''''' h0) (fun h0 : term968 _106189 _106193 k x y => @lem4417690 _106189 _106193 i'''' s i''''' k x y h1 h0 h2)). Qed.
Lemma lem4417693 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (y : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term212 _106189 _106193 s k x y) : False.
Proof. exact (ex_elim (@lem4412523 _106189 _106193 s k x y h2) (fun i''''' : _106193 => fun h0 : term211 _106189 _106193 s k x y i''''' => @lem4417692 _106189 _106193 i'''' s i''''' k x y h1 h0)). Qed.
Lemma lem4417694 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (k : _106193 -> Prop) (x : _106193 -> _106189) (h1 : term381 _106189 _106193 i'''') (h2 : term214 _106189 _106193 s k x) : False.
Proof. exact (ex_elim (@lem4412522 _106189 _106193 s k x h2) (fun y : _106193 -> _106189 => fun h0 : term213 _106189 _106193 s k x y => @lem4417693 _106189 _106193 i'''' s k x y h1 h0)). Qed.
Lemma lem4417695 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (s : type1470 _106189 _106193) (k : _106193 -> Prop) (h1 : term381 _106189 _106193 i'''') (h2 : term216 _106189 _106193 s k) : False.
Proof. exact (ex_elim (@lem4412521 _106189 _106193 s k h2) (fun x : _106193 -> _106189 => fun h0 : term215 _106189 _106193 s k x => @lem4417694 _106189 _106193 i'''' s k x h1 h0)). Qed.
Lemma lem4417696 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (k : _106193 -> Prop) (h1 : term381 _106189 _106193 i'''') (h2 : term218 _106189 _106193 k) : False.
Proof. exact (ex_elim (@lem4412520 _106189 _106193 k h2) (fun s : type1470 _106189 _106193 => fun h0 : term217 _106189 _106193 k s => @lem4417695 _106189 _106193 i'''' s k h1 h0)). Qed.
Lemma lem4417697 {_106189 _106193 : Type'} (i'''' : type844 _106189 _106193) (h1 : term381 _106189 _106193 i'''') (h2 : term10 _106189 _106193) : False.
Proof. exact (ex_elim (@lem4410679 _106189 _106193 h2) (fun k : _106193 -> Prop => fun h0 : term219 _106189 _106193 k => @lem4417696 _106189 _106193 i'''' k h1 h0)). Qed.
Lemma lem4417698 {_106189 _106193 : Type'} (h1 : term11 _106189 _106193) (h2 : term10 _106189 _106193) : False.
Proof. exact (ex_elim (@lem4411046 _106189 _106193 h1) (fun i'''' : type844 _106189 _106193 => fun h0 : term383 _106189 _106193 i'''' => @lem4417697 _106189 _106193 i'''' h0 h2)). Qed.
Lemma lem4417699 {_106189 _106193 A : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term10 _106189 _106193) : False.
Proof. exact (ex_elim (@lem4411413 _106193 A h2) (fun i''' : type614 _106193 A => fun h0 : term555 _106193 A i''' => @lem4417698 _106189 _106193 h1 h3)). Qed.
Lemma lem4417700 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term11 _106189 K) (h4 : term10 _106189 _106193) : False.
Proof. exact (ex_elim (@lem4411780 _106189 K h3) (fun i'' : type844 _106189 K => fun h0 : term383 _106189 K i'' => @lem4417699 _106189 _106193 A h1 h2 h4)). Qed.
Lemma lem4417701 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term11 _106189 K) (h4 : term14 _106189 _106193 K) (h5 : term10 _106189 _106193) : False.
Proof. exact (ex_elim (@lem4412147 _106189 _106193 K h4) (fun i' : type891 _106189 _106193 K => fun h0 : term727 _106189 _106193 K i' => @lem4417700 _106189 _106193 A K h1 h2 h3 h5)). Qed.
Lemma lem4417702 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term11 _106189 K) (h4 : term14 _106189 _106193 K) (h5 : term12 _106189 _106193 A) (h6 : term10 _106189 _106193) : False.
Proof. exact (ex_elim (@lem4412514 _106189 _106193 A h5) (fun i : type204 _106189 _106193 A => fun h0 : term903 _106189 _106193 A i => @lem4417701 _106189 _106193 A K h1 h2 h3 h4 h6)). Qed.
Lemma lem4417703 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term11 _106189 K) (h4 : term14 _106189 _106193 K) (h5 : term10 _106189 _106193) : term19 _106189 _106193 A.
Proof. exact (fun h0 : term12 _106189 _106193 A => @lem4417702 _106189 _106193 A K h1 h2 h3 h4 h0 h5). Qed.
Lemma lem4417704 {_106189 _106193 A : Type'} : (term19 _106189 _106193 A) = (term20 _106189 _106193 A).
Proof. exact (@lem69 (term12 _106189 _106193 A)). Qed.
Lemma lem4417705 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term11 _106189 K) (h4 : term14 _106189 _106193 K) (h5 : term10 _106189 _106193) : term20 _106189 _106193 A.
Proof. exact (EQ_MP (@lem4417704 _106189 _106193 A) (@lem4417703 _106189 _106193 A K h1 h2 h3 h4 h5)). Qed.
Lemma lem4417706 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term11 _106189 K) (h4 : term10 _106189 _106193) : term23 _106189 _106193 A K.
Proof. exact (fun h0 : term14 _106189 _106193 K => @lem4417705 _106189 _106193 A K h1 h2 h3 h0 h4). Qed.
Lemma lem4417707 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term13 _106193 A) (h3 : term10 _106189 _106193) : term26 _106189 _106193 A K.
Proof. exact (fun h0 : term11 _106189 K => @lem4417706 _106189 _106193 A K h1 h2 h0 h3). Qed.
Lemma lem4417708 {_106189 _106193 A K : Type'} (h1 : term11 _106189 _106193) (h2 : term10 _106189 _106193) : term29 _106189 _106193 A K.
Proof. exact (fun h0 : term13 _106193 A => @lem4417707 _106189 _106193 A K h1 h0 h2). Qed.
Lemma lem4417709 {_106189 _106193 A K : Type'} (h1 : term10 _106189 _106193) : term31 _106189 _106193 A K.
Proof. exact (fun h0 : term11 _106189 _106193 => @lem4417708 _106189 _106193 A K h0 h1). Qed.
Lemma lem4417710 {_106189 _106193 A K : Type'} : term33 _106189 _106193 A K.
Proof. exact (fun h0 : term10 _106189 _106193 => @lem4417709 _106189 _106193 A K h0). Qed.
Lemma lem4417711 {_106189 _106193 A K : Type'} : term15 _106189 _106193 A K.
Proof. exact (EQ_MP (@lem4410339 _106189 _106193 A K) (@lem4417710 _106189 _106193 A K)). Qed.
Lemma lem4417713 {_106189 _106193 A K : Type'} : term15 _106189 _106193 A K.
Proof. exact (@lem4409685 _106189 _106193 A K (@lem4417711 _106189 _106193 A K)). Qed.
Lemma lem4417714 {_106189 _106193 A K : Type'} (h1 : term10 _106189 _106193) : term30 _106189 _106193 A K.
Proof. exact (@lem4417713 _106189 _106193 A K (@lem4409662 _106189 _106193 h1)). Qed.
Lemma lem4417715 {_106189 _106193 A K : Type'} (h1 : term10 _106189 _106193) : term28 _106189 _106193 A K.
Proof. exact (@lem4417714 _106189 _106193 A K h1 (@lem4409663 _106189 _106193)). Qed.
Lemma lem4417716 {_106189 _106193 A K : Type'} (h1 : term10 _106189 _106193) : term25 _106189 _106193 A K.
Proof. exact (@lem4417715 _106189 _106193 A K h1 (@lem4409666 _106193 A)). Qed.
Lemma lem4417717 {_106189 _106193 A K : Type'} (h1 : term10 _106189 _106193) : term22 _106189 _106193 A K.
Proof. exact (@lem4417716 _106189 _106193 A K h1 (@lem4409668 _106189 K)). Qed.
Lemma lem4417718 {_106189 _106193 A : Type'} (h1 : term10 _106189 _106193) : term19 _106189 _106193 A.
Proof. exact (@lem4417717 _106189 _106193 A Prop h1 (@lem4409667 _106189 _106193 Prop)). Qed.
Lemma lem4417719 {_106189 _106193 : Type'} (h1 : term10 _106189 _106193) : False.
Proof. exact (@lem4417718 _106189 _106193 Prop h1 (@lem4409665 _106189 _106193 Prop)). Qed.
Lemma lem4417720 {_106189 _106193 : Type'} (h1 : term10 _106189 _106193) : (term10 _106189 _106193) = False.
Proof. exact (prop_ext (fun h2 : term10 _106189 _106193 => @lem4417719 _106189 _106193 h1) (fun h2 : False => @lem4409662 _106189 _106193 h1)). Qed.
Lemma lem4417721 {_106189 _106193 : Type'} (h1 : term10 _106189 _106193) : False.
Proof. exact (EQ_MP (@lem4417720 _106189 _106193 h1) (@lem4409662 _106189 _106193 h1)). Qed.
Lemma lem4417722 {_106189 _106193 : Type'} : term9 _106189 _106193.
Proof. exact (fun h0 : term10 _106189 _106193 => @lem4417721 _106189 _106193 h0). Qed.
Lemma lem4417723 {_106189 _106193 : Type'} : term8 _106189 _106193.
Proof. exact (EQ_MP (@lem4409661 _106189 _106193) (@lem4417722 _106189 _106193)). Qed.
