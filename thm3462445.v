Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3462445_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3458986_spec.
Lemma lem3460804 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3460805 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term1 _89769 _89788 _89789 P f) = (term2 _89769 _89788 _89789 P f).
Proof. exact (@lem3460804 (term1 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460806 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term2 _89769 _89788 _89789 P f) = (term1 _89769 _89788 _89789 P f).
Proof. exact (SYM (@lem3460805 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460807 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term3 _89769 _89788 _89789 P f) : term3 _89769 _89788 _89789 P f.
Proof. exact (h1). Qed.
Lemma lem3460810 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term2 _89769 _89788 _89789 P f) : term2 _89769 _89788 _89789 P f.
Proof. exact (h1). Qed.
Lemma lem3460811 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term4 _89769 _89788 _89789 P f.
Proof. exact (fun h0 : term2 _89769 _89788 _89789 P f => @lem3460810 _89769 _89788 _89789 P f h0). Qed.
Lemma lem3460812 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term4 _89769 _89788 _89789 P f) : term4 _89769 _89788 _89789 P f.
Proof. exact (h1). Qed.
Lemma lem3460813 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term2 _89769 _89788 _89789 P f) : term2 _89769 _89788 _89789 P f.
Proof. exact (h1). Qed.
Lemma lem3460814 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term2 _89769 _89788 _89789 P f) (h2 : term4 _89769 _89788 _89789 P f) : term2 _89769 _89788 _89789 P f.
Proof. exact (@lem3460812 _89769 _89788 _89789 P f h2 (@lem3460813 _89769 _89788 _89789 P f h1)). Qed.
Lemma lem3460815 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term2 _89769 _89788 _89789 P f) : term5 _89769 _89788 _89789 P f.
Proof. exact (fun h0 : term4 _89769 _89788 _89789 P f => @lem3460814 _89769 _89788 _89789 P f h1 h0). Qed.
Lemma lem3460816 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term4 _89769 _89788 _89789 P f) : term4 _89769 _89788 _89789 P f.
Proof. exact (h1). Qed.
Lemma lem3460817 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term2 _89769 _89788 _89789 P f) (h2 : term4 _89769 _89788 _89789 P f) : term2 _89769 _89788 _89789 P f.
Proof. exact (@lem3460815 _89769 _89788 _89789 P f h1 (@lem3460816 _89769 _89788 _89789 P f h2)). Qed.
Lemma lem3460818 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term4 _89769 _89788 _89789 P f) : term4 _89769 _89788 _89789 P f.
Proof. exact (fun h0 : term2 _89769 _89788 _89789 P f => @lem3460817 _89769 _89788 _89789 P f h0 h1). Qed.
Lemma lem3460819 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term6 _89769 _89788 _89789 P f.
Proof. exact (fun h0 : term4 _89769 _89788 _89789 P f => @lem3460818 _89769 _89788 _89789 P f h0). Qed.
Lemma lem3460822 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term4 _89769 _89788 _89789 P f.
Proof. exact (@lem3460819 _89769 _89788 _89789 P f (@lem3460811 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460823 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term4 _89769 _89788 _89789 P f.
Proof. exact (@lem3460822 _89769 _89788 _89789 P f). Qed.
Lemma lem3460833 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3460834 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term2 _89769 _89788 _89789 P f) = (term7 _89769 _89788 _89789 P f).
Proof. exact (@lem3460833 (term3 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460836 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3460837 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term7 _89769 _89788 _89789 P f) = (term1 _89769 _89788 _89789 P f).
Proof. exact (@lem3460836 (term1 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460842 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term2 _89769 _89788 _89789 P f) = (term1 _89769 _89788 _89789 P f).
Proof. exact (TRANS (@lem3460834 _89769 _89788 _89789 P f) (@lem3460837 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460913 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : (term9 _89769 _89788 _89789 f) = (term10 _89769 _89788 _89789 f).
Proof. exact (fun_ext (fun P : type1470 _89788 _89789 => @lem3460842 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460914 {_89788 _89789 : Type'} : (@all (_89789 -> _89788 -> Prop)) = (@all (_89789 -> _89788 -> Prop)).
Proof. exact (eq_refl (@all (_89789 -> _89788 -> Prop))). Qed.
Lemma lem3460915 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : (term11 _89769 _89788 _89789 f) = (term12 _89769 _89788 _89789 f).
Proof. exact (MK_COMB (@lem3460914 _89788 _89789) (@lem3460913 _89769 _89788 _89789 f)). Qed.
Lemma lem3460920 {_89769 _89788 _89789 : Type'} : (term13 _89769 _89788 _89789) = (term14 _89769 _89788 _89789).
Proof. exact (fun_ext (fun f : type1517 _89769 _89788 _89789 => @lem3460915 _89769 _89788 _89789 f)). Qed.
Lemma lem3460921 {_89769 _89788 _89789 : Type'} : (@all (_89789 -> _89788 -> _89769 -> Prop)) = (@all (_89789 -> _89788 -> _89769 -> Prop)).
Proof. exact (eq_refl (@all (_89789 -> _89788 -> _89769 -> Prop))). Qed.
Lemma lem3460930 {_89769 _89788 _89789 : Type'} : (term15 _89769 _89788 _89789) = (term16 _89769 _89788 _89789).
Proof. exact (MK_COMB (@lem3460921 _89769 _89788 _89789) (@lem3460920 _89769 _89788 _89789)). Qed.
Lemma lem3460935 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term17 _89769 _89788 _89789 P x f x' y) = (term17 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term17 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3460936 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term18 _89769 _89788 _89789 P x f x') = (term18 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3460935 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3460937 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3460938 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term19 _89769 _89788 _89789 P x f x') = (term19 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3460937 _89788) (@lem3460936 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3460939 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term20 _89769 _89788 _89789 P x f) = (term20 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3460938 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3460940 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3460941 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term21 _89769 _89788 _89789 P x f) = (term21 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3460940 _89789) (@lem3460939 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3460942 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3460947 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term22 _89769 _89788 _89789 P t f x y) = (term22 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term22 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3460948 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term23 _89769 _89788 _89789 P t f x) = (term23 _89769 _89788 _89789 P t f x).
Proof. exact (fun_ext (fun y : _89788 => @lem3460947 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3460949 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3460950 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term24 _89769 _89788 _89789 P t f x) = (term24 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3460949 _89788) (@lem3460948 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3460951 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term25 _89769 _89788 _89789 P t f) = (term25 _89769 _89788 _89789 P t f).
Proof. exact (fun_ext (fun x : _89789 => @lem3460950 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3460952 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3460953 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term26 _89769 _89788 _89789 P t f) = (term26 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3460952 _89789) (@lem3460951 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3460954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3460955 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term27 _89769 _89788 _89789 P t f) = (term27 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3460954) (@lem3460953 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3460956 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term28 _89769 _89788 _89789 P f x t) = (term28 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3460955 _89769 _89788 _89789 P t f) (@lem3460942 _89769 x t)). Qed.
Lemma lem3460957 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term29 _89769 _89788 _89789 P f x) = (term29 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3460956 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3460958 {_89769 : Type'} : (@all (_89769 -> Prop)) = (@all (_89769 -> Prop)).
Proof. exact (eq_refl (@all (_89769 -> Prop))). Qed.
Lemma lem3460959 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term30 _89769 _89788 _89789 P f x) = (term30 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3460958 _89769) (@lem3460957 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3460960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460961 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term31 _89769 _89788 _89789 P f x) = (term31 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3460960) (@lem3460959 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3460962 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term30 _89769 _89788 _89789 P f x) = (term21 _89769 _89788 _89789 P x f)) = ((term30 _89769 _89788 _89789 P f x) = (term21 _89769 _89788 _89789 P x f)).
Proof. exact (MK_COMB (@lem3460961 _89769 _89788 _89789 P f x) (@lem3460941 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3460963 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term32 _89769 _89788 _89789 P f) = (term32 _89769 _89788 _89789 P f).
Proof. exact (fun_ext (fun x : _89769 => @lem3460962 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3460964 {_89769 : Type'} : (@all _89769) = (@all _89769).
Proof. exact (eq_refl (@all _89769)). Qed.
Lemma lem3460965 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term1 _89769 _89788 _89789 P f) = (term1 _89769 _89788 _89789 P f).
Proof. exact (MK_COMB (@lem3460964 _89769) (@lem3460963 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460966 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : (term10 _89769 _89788 _89789 f) = (term10 _89769 _89788 _89789 f).
Proof. exact (fun_ext (fun P : type1470 _89788 _89789 => @lem3460965 _89769 _89788 _89789 P f)). Qed.
Lemma lem3460967 {_89788 _89789 : Type'} : (@all (_89789 -> _89788 -> Prop)) = (@all (_89789 -> _89788 -> Prop)).
Proof. exact (eq_refl (@all (_89789 -> _89788 -> Prop))). Qed.
Lemma lem3460968 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : (term12 _89769 _89788 _89789 f) = (term12 _89769 _89788 _89789 f).
Proof. exact (MK_COMB (@lem3460967 _89788 _89789) (@lem3460966 _89769 _89788 _89789 f)). Qed.
Lemma lem3460969 {_89769 _89788 _89789 : Type'} : (term14 _89769 _89788 _89789) = (term14 _89769 _89788 _89789).
Proof. exact (fun_ext (fun f : type1517 _89769 _89788 _89789 => @lem3460968 _89769 _89788 _89789 f)). Qed.
Lemma lem3460970 {_89769 _89788 _89789 : Type'} : (@all (_89789 -> _89788 -> _89769 -> Prop)) = (@all (_89789 -> _89788 -> _89769 -> Prop)).
Proof. exact (eq_refl (@all (_89789 -> _89788 -> _89769 -> Prop))). Qed.
Lemma lem3460971 {_89769 _89788 _89789 : Type'} : (term16 _89769 _89788 _89789) = (term16 _89769 _89788 _89789).
Proof. exact (MK_COMB (@lem3460970 _89769 _89788 _89789) (@lem3460969 _89769 _89788 _89789)). Qed.
Lemma lem3461028 {_89769 _89788 _89789 : Type'} : (term15 _89769 _89788 _89789) = (term16 _89769 _89788 _89789).
Proof. exact (TRANS (@lem3460930 _89769 _89788 _89789) (@lem3460971 _89769 _89788 _89789)). Qed.
Lemma lem3461029 {_89769 _89788 _89789 : Type'} : (term16 _89769 _89788 _89789) = (term15 _89769 _89788 _89789).
Proof. exact (SYM (@lem3461028 _89769 _89788 _89789)). Qed.
Lemma lem3461031 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3461032 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term30 _89769 _89788 _89789 P f x) = (term21 _89769 _89788 _89789 P x f)) = (term33 _89769 _89788 _89789 P x f).
Proof. exact (@lem3461031 ((term30 _89769 _89788 _89789 P f x) = (term21 _89769 _89788 _89789 P x f))). Qed.
Lemma lem3461033 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term33 _89769 _89788 _89789 P x f) = ((term30 _89769 _89788 _89789 P f x) = (term21 _89769 _89788 _89789 P x f)).
Proof. exact (SYM (@lem3461032 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461034 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term34 _89769 _89788 _89789 P x f) : term34 _89769 _89788 _89789 P x f.
Proof. exact (h1). Qed.
Lemma lem3461043 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term35 _89769 _89788 _89789 P t f x y) = (term36 _89769 _89788 _89789 P t f x y).
Proof. exact (@lem17045 (P x y) (t = (f x y))). Qed.
Lemma lem3461046 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term22 _89769 _89788 _89789 P t f x y) = (term22 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term22 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461047 {_89788 : Type'} (P : _89788 -> Prop) : (term37 _89788 P) = (term38 _89788 P).
Proof. exact (@lem18394 _89788 P). Qed.
Lemma lem3461048 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term39 _89769 _89788 _89789 P t f x) = (term40 _89769 _89788 _89789 P t f x).
Proof. exact (@lem3461047 _89788 (term23 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461049 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term41 _89769 _89788 _89789 P t f x y) = (term22 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term41 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3461051 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term42 _89769 _89788 _89789 P t f x y) = (term35 _89769 _89788 _89789 P t f x y).
Proof. exact (MK_COMB (@lem3461050) (@lem3461049 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461052 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term42 _89769 _89788 _89789 P t f x y) = (term36 _89769 _89788 _89789 P t f x y).
Proof. exact (TRANS (@lem3461051 _89769 _89788 _89789 P t f x y) (@lem3461043 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461053 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term43 _89769 _89788 _89789 P t f x) = (term44 _89769 _89788 _89789 P t f x).
Proof. exact (fun_ext (fun y : _89788 => @lem3461052 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461054 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3461055 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term40 _89769 _89788 _89789 P t f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461054 _89788) (@lem3461053 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461056 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term39 _89769 _89788 _89789 P t f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (TRANS (@lem3461048 _89769 _89788 _89789 P t f x) (@lem3461055 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461057 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term23 _89769 _89788 _89789 P t f x) = (term23 _89769 _89788 _89789 P t f x).
Proof. exact (fun_ext (fun y : _89788 => @lem3461046 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461058 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461059 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term24 _89769 _89788 _89789 P t f x) = (term24 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461058 _89788) (@lem3461057 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461060 {_89789 : Type'} (P : _89789 -> Prop) : (term37 _89789 P) = (term38 _89789 P).
Proof. exact (@lem18394 _89789 P). Qed.
Lemma lem3461061 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term46 _89769 _89788 _89789 P t f) = (term47 _89769 _89788 _89789 P t f).
Proof. exact (@lem3461060 _89789 (term25 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461062 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term48 _89769 _89788 _89789 P t f x) = (term24 _89769 _89788 _89789 P t f x).
Proof. exact (eq_refl (term48 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3461064 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term49 _89769 _89788 _89789 P t f x) = (term39 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461063) (@lem3461062 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461065 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term49 _89769 _89788 _89789 P t f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (TRANS (@lem3461064 _89769 _89788 _89789 P t f x) (@lem3461056 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461066 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term50 _89769 _89788 _89789 P t f) = (term51 _89769 _89788 _89789 P t f).
Proof. exact (fun_ext (fun x : _89789 => @lem3461065 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461067 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461068 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term47 _89769 _89788 _89789 P t f) = (term52 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461067 _89789) (@lem3461066 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461069 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term46 _89769 _89788 _89789 P t f) = (term52 _89769 _89788 _89789 P t f).
Proof. exact (TRANS (@lem3461061 _89769 _89788 _89789 P t f) (@lem3461068 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461070 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term25 _89769 _89788 _89789 P t f) = (term25 _89769 _89788 _89789 P t f).
Proof. exact (fun_ext (fun x : _89789 => @lem3461059 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461071 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461072 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term26 _89769 _89788 _89789 P t f) = (term26 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461071 _89789) (@lem3461070 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461073 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term53 _89769 x t) = (term53 _89769 x t).
Proof. exact (eq_refl (term53 _89769 x t)). Qed.
Lemma lem3461074 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3461075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461076 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term54 _89769 _89788 _89789 P t f) = (term54 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461075) (@lem3461072 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461077 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term55 _89769 _89788 _89789 P f x t) = (term55 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461076 _89769 _89788 _89789 P t f) (@lem3461073 _89769 x t)). Qed.
Lemma lem3461078 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term56 _89769 _89788 _89789 P f x t) = (term55 _89769 _89788 _89789 P f x t).
Proof. exact (@lem17362 (term26 _89769 _89788 _89789 P t f) (@IN _89769 x t)). Qed.
Lemma lem3461079 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term56 _89769 _89788 _89789 P f x t) = (term55 _89769 _89788 _89789 P f x t).
Proof. exact (TRANS (@lem3461078 _89769 _89788 _89789 P f x t) (@lem3461077 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461081 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term57 _89769 _89788 _89789 P t f) = (term58 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461080) (@lem3461069 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461082 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term59 _89769 _89788 _89789 P f x t) = (term60 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461081 _89769 _89788 _89789 P t f) (@lem3461074 _89769 x t)). Qed.
Lemma lem3461083 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term28 _89769 _89788 _89789 P f x t) = (term59 _89769 _89788 _89789 P f x t).
Proof. exact (@lem17265 (term26 _89769 _89788 _89789 P t f) (@IN _89769 x t)). Qed.
Lemma lem3461084 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term28 _89769 _89788 _89789 P f x t) = (term60 _89769 _89788 _89789 P f x t).
Proof. exact (TRANS (@lem3461083 _89769 _89788 _89789 P f x t) (@lem3461082 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461085 {_89769 : Type'} (P : type686 _89769) : (term61 _89769 P) = (term62 _89769 P).
Proof. exact (@lem18392 (_89769 -> Prop) P). Qed.
Lemma lem3461086 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term63 _89769 _89788 _89789 P f x) = (term64 _89769 _89788 _89789 P f x).
Proof. exact (@lem3461085 _89769 (term29 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461087 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term65 _89769 _89788 _89789 P f x t) = (term28 _89769 _89788 _89789 P f x t).
Proof. exact (eq_refl (term65 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3461089 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term66 _89769 _89788 _89789 P f x t) = (term56 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461088) (@lem3461087 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461090 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term66 _89769 _89788 _89789 P f x t) = (term55 _89769 _89788 _89789 P f x t).
Proof. exact (TRANS (@lem3461089 _89769 _89788 _89789 P f x t) (@lem3461079 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461091 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term67 _89769 _89788 _89789 P f x) = (term68 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461090 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461092 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461093 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term64 _89769 _89788 _89789 P f x) = (term69 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461092 _89769) (@lem3461091 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461094 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term63 _89769 _89788 _89789 P f x) = (term69 _89769 _89788 _89789 P f x).
Proof. exact (TRANS (@lem3461086 _89769 _89788 _89789 P f x) (@lem3461093 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461095 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term29 _89769 _89788 _89789 P f x) = (term70 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461084 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461096 {_89769 : Type'} : (@all (_89769 -> Prop)) = (@all (_89769 -> Prop)).
Proof. exact (eq_refl (@all (_89769 -> Prop))). Qed.
Lemma lem3461097 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term30 _89769 _89788 _89789 P f x) = (term71 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461096 _89769) (@lem3461095 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461106 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term72 _89769 _89788 _89789 P x f x' y) = (term73 _89769 _89788 _89789 P x f x' y).
Proof. exact (@lem17362 (P x' y) (term74 _89769 _89788 _89789 x f x' y)). Qed.
Lemma lem3461111 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term17 _89769 _89788 _89789 P x f x' y) = (term75 _89769 _89788 _89789 P x f x' y).
Proof. exact (@lem17265 (P x' y) (term74 _89769 _89788 _89789 x f x' y)). Qed.
Lemma lem3461112 {_89788 : Type'} (P : _89788 -> Prop) : (term76 _89788 P) = (term77 _89788 P).
Proof. exact (@lem18392 _89788 P). Qed.
Lemma lem3461113 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term78 _89769 _89788 _89789 P x f x') = (term79 _89769 _89788 _89789 P x f x').
Proof. exact (@lem3461112 _89788 (term18 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461114 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term80 _89769 _89788 _89789 P x f x' y) = (term17 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term80 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461115 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3461116 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term81 _89769 _89788 _89789 P x f x' y) = (term72 _89769 _89788 _89789 P x f x' y).
Proof. exact (MK_COMB (@lem3461115) (@lem3461114 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461117 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term81 _89769 _89788 _89789 P x f x' y) = (term73 _89769 _89788 _89789 P x f x' y).
Proof. exact (TRANS (@lem3461116 _89769 _89788 _89789 P x f x' y) (@lem3461106 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461118 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term82 _89769 _89788 _89789 P x f x') = (term83 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3461117 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461119 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461120 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term79 _89769 _89788 _89789 P x f x') = (term84 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461119 _89788) (@lem3461118 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461121 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term78 _89769 _89788 _89789 P x f x') = (term84 _89769 _89788 _89789 P x f x').
Proof. exact (TRANS (@lem3461113 _89769 _89788 _89789 P x f x') (@lem3461120 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461122 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term18 _89769 _89788 _89789 P x f x') = (term85 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3461111 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461123 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3461124 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term19 _89769 _89788 _89789 P x f x') = (term86 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461123 _89788) (@lem3461122 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461125 {_89789 : Type'} (P : _89789 -> Prop) : (term76 _89789 P) = (term77 _89789 P).
Proof. exact (@lem18392 _89789 P). Qed.
Lemma lem3461126 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term87 _89769 _89788 _89789 P x f) = (term88 _89769 _89788 _89789 P x f).
Proof. exact (@lem3461125 _89789 (term20 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461127 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term89 _89769 _89788 _89789 P x f x') = (term19 _89769 _89788 _89789 P x f x').
Proof. exact (eq_refl (term89 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3461129 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term90 _89769 _89788 _89789 P x f x') = (term78 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461128) (@lem3461127 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461130 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term90 _89769 _89788 _89789 P x f x') = (term84 _89769 _89788 _89789 P x f x').
Proof. exact (TRANS (@lem3461129 _89769 _89788 _89789 P x f x') (@lem3461121 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461131 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term91 _89769 _89788 _89789 P x f) = (term92 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461130 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461132 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461133 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term88 _89769 _89788 _89789 P x f) = (term93 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461132 _89789) (@lem3461131 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461134 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term87 _89769 _89788 _89789 P x f) = (term93 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461126 _89769 _89788 _89789 P x f) (@lem3461133 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461135 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term20 _89769 _89788 _89789 P x f) = (term94 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461124 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461136 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461137 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term21 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461136 _89789) (@lem3461135 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461139 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term96 _89769 _89788 _89789 P f x) = (term97 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461138) (@lem3461094 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461140 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term98 _89769 _89788 _89789 P x f) = (term99 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461139 _89769 _89788 _89789 P f x) (@lem3461137 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461142 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term100 _89769 _89788 _89789 P f x) = (term101 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461141) (@lem3461097 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461143 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term102 _89769 _89788 _89789 P x f) = (term103 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461142 _89769 _89788 _89789 P f x) (@lem3461134 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461145 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term104 _89769 _89788 _89789 P x f) = (term105 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461144) (@lem3461143 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461146 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term106 _89769 _89788 _89789 P x f) = (term107 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461145 _89769 _89788 _89789 P x f) (@lem3461140 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461147 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term34 _89769 _89788 _89789 P x f) = (term106 _89769 _89788 _89789 P x f).
Proof. exact (@lem17646 (term30 _89769 _89788 _89789 P f x) (term21 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461148 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term34 _89769 _89788 _89789 P x f) = (term107 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461147 _89769 _89788 _89789 P x f) (@lem3461146 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3461456 {_89789 : Type'} (P : Prop) (Q : _89789 -> Prop) : (term108 _89789 P Q) = (term109 _89789 P Q).
Proof. exact (@lem3461455 _89789 P Q). Qed.
Lemma lem3461457 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term110 _89769 _89788 _89789 P x f) = (term111 _89769 _89788 _89789 P x f).
Proof. exact (@lem3461456 _89789 (term71 _89769 _89788 _89789 P f x) (term92 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461458 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term112 _89769 _89788 _89789 P x f x') = (term84 _89769 _89788 _89789 P x f x').
Proof. exact (eq_refl (term112 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461459 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term113 _89769 _89788 _89789 P x f) = (term92 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461458 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461460 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461461 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term114 _89769 _89788 _89789 P x f) = (term93 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461460 _89789) (@lem3461459 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461462 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term101 _89769 _89788 _89789 P f x) = (term101 _89769 _89788 _89789 P f x).
Proof. exact (eq_refl (term101 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461463 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term110 _89769 _89788 _89789 P x f) = (term103 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461462 _89769 _89788 _89789 P f x) (@lem3461461 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461465 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term115 _89769 _89788 _89789 P x f) = (term116 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461464) (@lem3461463 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461466 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term112 _89769 _89788 _89789 P x f x') = (term84 _89769 _89788 _89789 P x f x').
Proof. exact (eq_refl (term112 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461467 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term101 _89769 _89788 _89789 P f x) = (term101 _89769 _89788 _89789 P f x).
Proof. exact (eq_refl (term101 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461468 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term117 _89769 _89788 _89789 P x f x') = (term118 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461467 _89769 _89788 _89789 P f x) (@lem3461466 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461469 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term119 _89769 _89788 _89789 P x f) = (term120 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461468 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461470 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461471 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term111 _89769 _89788 _89789 P x f) = (term121 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461470 _89789) (@lem3461469 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461472 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term110 _89769 _89788 _89789 P x f) = (term111 _89769 _89788 _89789 P x f)) = ((term103 _89769 _89788 _89789 P x f) = (term121 _89769 _89788 _89789 P x f)).
Proof. exact (MK_COMB (@lem3461465 _89769 _89788 _89789 P x f) (@lem3461471 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461473 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term103 _89769 _89788 _89789 P x f) = (term121 _89769 _89788 _89789 P x f).
Proof. exact (EQ_MP (@lem3461472 _89769 _89788 _89789 P x f) (@lem3461457 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461475 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3461476 {_89788 : Type'} (P : Prop) (Q : _89788 -> Prop) : (term108 _89788 P Q) = (term109 _89788 P Q).
Proof. exact (@lem3461475 _89788 P Q). Qed.
Lemma lem3461477 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term122 _89769 _89788 _89789 P x f x') = (term123 _89769 _89788 _89789 P x f x').
Proof. exact (@lem3461476 _89788 (term71 _89769 _89788 _89789 P f x) (term83 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461478 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term124 _89769 _89788 _89789 P x f x' y) = (term73 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term124 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461479 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term125 _89769 _89788 _89789 P x f x') = (term83 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3461478 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461480 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461481 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term126 _89769 _89788 _89789 P x f x') = (term84 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461480 _89788) (@lem3461479 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461482 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term101 _89769 _89788 _89789 P f x) = (term101 _89769 _89788 _89789 P f x).
Proof. exact (eq_refl (term101 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461483 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term122 _89769 _89788 _89789 P x f x') = (term118 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461482 _89769 _89788 _89789 P f x) (@lem3461481 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461485 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term127 _89769 _89788 _89789 P x f x') = (term128 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461484) (@lem3461483 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461486 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term124 _89769 _89788 _89789 P x f x' y) = (term73 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term124 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461487 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term101 _89769 _89788 _89789 P f x) = (term101 _89769 _89788 _89789 P f x).
Proof. exact (eq_refl (term101 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461488 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term129 _89769 _89788 _89789 P x f x' y) = (term130 _89769 _89788 _89789 P x f x' y).
Proof. exact (MK_COMB (@lem3461487 _89769 _89788 _89789 P f x) (@lem3461486 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461489 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term131 _89769 _89788 _89789 P x f x') = (term132 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3461488 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461490 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461491 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term123 _89769 _89788 _89789 P x f x') = (term133 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461490 _89788) (@lem3461489 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461492 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : ((term122 _89769 _89788 _89789 P x f x') = (term123 _89769 _89788 _89789 P x f x')) = ((term118 _89769 _89788 _89789 P x f x') = (term133 _89769 _89788 _89789 P x f x')).
Proof. exact (MK_COMB (@lem3461485 _89769 _89788 _89789 P x f x') (@lem3461491 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461493 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term118 _89769 _89788 _89789 P x f x') = (term133 _89769 _89788 _89789 P x f x').
Proof. exact (EQ_MP (@lem3461492 _89769 _89788 _89789 P x f x') (@lem3461477 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461494 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term120 _89769 _89788 _89789 P x f) = (term134 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461493 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461495 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461496 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term121 _89769 _89788 _89789 P x f) = (term135 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461495 _89789) (@lem3461494 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461497 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term103 _89769 _89788 _89789 P x f) = (term135 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461473 _89769 _89788 _89789 P x f) (@lem3461496 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461499 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term105 _89769 _89788 _89789 P x f) = (term136 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461498) (@lem3461497 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461501 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3461502 {_89789 : Type'} (P : _89789 -> Prop) (Q : Prop) : (term137 _89789 P Q) = (term138 _89789 P Q).
Proof. exact (@lem3461501 _89789 P Q). Qed.
Lemma lem3461503 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term139 _89769 _89788 _89789 P f x t) = (term140 _89769 _89788 _89789 P f x t).
Proof. exact (@lem3461502 _89789 (term25 _89769 _89788 _89789 P t f) (term53 _89769 x t)). Qed.
Lemma lem3461504 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term48 _89769 _89788 _89789 P t f x) = (term24 _89769 _89788 _89789 P t f x).
Proof. exact (eq_refl (term48 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461505 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term141 _89769 _89788 _89789 P t f) = (term25 _89769 _89788 _89789 P t f).
Proof. exact (fun_ext (fun x : _89789 => @lem3461504 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461506 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461507 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term142 _89769 _89788 _89789 P t f) = (term26 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461506 _89789) (@lem3461505 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461509 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term143 _89769 _89788 _89789 P t f) = (term54 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461508) (@lem3461507 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461510 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term53 _89769 x t) = (term53 _89769 x t).
Proof. exact (eq_refl (term53 _89769 x t)). Qed.
Lemma lem3461511 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term139 _89769 _89788 _89789 P f x t) = (term55 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461509 _89769 _89788 _89789 P t f) (@lem3461510 _89769 x t)). Qed.
Lemma lem3461512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461513 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term144 _89769 _89788 _89789 P f x t) = (term145 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461512) (@lem3461511 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461514 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term48 _89769 _89788 _89789 P t f x) = (term24 _89769 _89788 _89789 P t f x).
Proof. exact (eq_refl (term48 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461516 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term146 _89769 _89788 _89789 P t f x) = (term147 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461515) (@lem3461514 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461517 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term53 _89769 x t) = (term53 _89769 x t).
Proof. exact (eq_refl (term53 _89769 x t)). Qed.
Lemma lem3461518 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term148 _89769 _89788 _89789 P f x x' t) = (term149 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461516 _89769 _89788 _89789 P t f x) (@lem3461517 _89769 x' t)). Qed.
Lemma lem3461519 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term150 _89769 _89788 _89789 P f x t) = (term151 _89769 _89788 _89789 P f x t).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461518 _89769 _89788 _89789 P f x' x t)). Qed.
Lemma lem3461520 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461521 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term140 _89769 _89788 _89789 P f x t) = (term152 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461520 _89789) (@lem3461519 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461522 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : ((term139 _89769 _89788 _89789 P f x t) = (term140 _89769 _89788 _89789 P f x t)) = ((term55 _89769 _89788 _89789 P f x t) = (term152 _89769 _89788 _89789 P f x t)).
Proof. exact (MK_COMB (@lem3461513 _89769 _89788 _89789 P f x t) (@lem3461521 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461523 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term55 _89769 _89788 _89789 P f x t) = (term152 _89769 _89788 _89789 P f x t).
Proof. exact (EQ_MP (@lem3461522 _89769 _89788 _89789 P f x t) (@lem3461503 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461525 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3461526 {_89788 : Type'} (P : _89788 -> Prop) (Q : Prop) : (term137 _89788 P Q) = (term138 _89788 P Q).
Proof. exact (@lem3461525 _89788 P Q). Qed.
Lemma lem3461527 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term153 _89769 _89788 _89789 P f x x' t) = (term154 _89769 _89788 _89789 P f x x' t).
Proof. exact (@lem3461526 _89788 (term23 _89769 _89788 _89789 P t f x) (term53 _89769 x' t)). Qed.
Lemma lem3461528 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term41 _89769 _89788 _89789 P t f x y) = (term22 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term41 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461529 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term155 _89769 _89788 _89789 P t f x) = (term23 _89769 _89788 _89789 P t f x).
Proof. exact (fun_ext (fun y : _89788 => @lem3461528 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461530 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461531 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term156 _89769 _89788 _89789 P t f x) = (term24 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461530 _89788) (@lem3461529 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461533 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term157 _89769 _89788 _89789 P t f x) = (term147 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461532) (@lem3461531 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461534 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term53 _89769 x t) = (term53 _89769 x t).
Proof. exact (eq_refl (term53 _89769 x t)). Qed.
Lemma lem3461535 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term153 _89769 _89788 _89789 P f x x' t) = (term149 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461533 _89769 _89788 _89789 P t f x) (@lem3461534 _89769 x' t)). Qed.
Lemma lem3461536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461537 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term158 _89769 _89788 _89789 P f x x' t) = (term159 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461536) (@lem3461535 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461538 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term41 _89769 _89788 _89789 P t f x y) = (term22 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term41 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461540 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term160 _89769 _89788 _89789 P t f x y) = (term161 _89769 _89788 _89789 P t f x y).
Proof. exact (MK_COMB (@lem3461539) (@lem3461538 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461541 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term53 _89769 x t) = (term53 _89769 x t).
Proof. exact (eq_refl (term53 _89769 x t)). Qed.
Lemma lem3461542 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) (x' : _89769) (t : _89769 -> Prop) : (term162 _89769 _89788 _89789 P f x y x' t) = (term163 _89769 _89788 _89789 P f x y x' t).
Proof. exact (MK_COMB (@lem3461540 _89769 _89788 _89789 P t f x y) (@lem3461541 _89769 x' t)). Qed.
Lemma lem3461543 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term164 _89769 _89788 _89789 P f x x' t) = (term165 _89769 _89788 _89789 P f x x' t).
Proof. exact (fun_ext (fun y : _89788 => @lem3461542 _89769 _89788 _89789 P f x y x' t)). Qed.
Lemma lem3461544 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461545 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term154 _89769 _89788 _89789 P f x x' t) = (term166 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461544 _89788) (@lem3461543 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461546 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : ((term153 _89769 _89788 _89789 P f x x' t) = (term154 _89769 _89788 _89789 P f x x' t)) = ((term149 _89769 _89788 _89789 P f x x' t) = (term166 _89769 _89788 _89789 P f x x' t)).
Proof. exact (MK_COMB (@lem3461537 _89769 _89788 _89789 P f x x' t) (@lem3461545 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461547 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term149 _89769 _89788 _89789 P f x x' t) = (term166 _89769 _89788 _89789 P f x x' t).
Proof. exact (EQ_MP (@lem3461546 _89769 _89788 _89789 P f x x' t) (@lem3461527 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461548 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term151 _89769 _89788 _89789 P f x t) = (term167 _89769 _89788 _89789 P f x t).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461547 _89769 _89788 _89789 P f x' x t)). Qed.
Lemma lem3461549 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461550 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term152 _89769 _89788 _89789 P f x t) = (term168 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461549 _89789) (@lem3461548 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461551 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term55 _89769 _89788 _89789 P f x t) = (term168 _89769 _89788 _89789 P f x t).
Proof. exact (TRANS (@lem3461523 _89769 _89788 _89789 P f x t) (@lem3461550 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461552 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term68 _89769 _89788 _89789 P f x) = (term169 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461551 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461553 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461554 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term69 _89769 _89788 _89789 P f x) = (term170 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461553 _89769) (@lem3461552 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461556 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term97 _89769 _89788 _89789 P f x) = (term171 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461555) (@lem3461554 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461557 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461558 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term99 _89769 _89788 _89789 P x f) = (term172 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461556 _89769 _89788 _89789 P f x) (@lem3461557 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461560 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3461561 {_89769 : Type'} (P : type686 _89769) (Q : Prop) : (term173 _89769 P Q) = (term174 _89769 P Q).
Proof. exact (@lem3461560 (_89769 -> Prop) P Q). Qed.
Lemma lem3461562 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term175 _89769 _89788 _89789 P x f) = (term176 _89769 _89788 _89789 P x f).
Proof. exact (@lem3461561 _89769 (term169 _89769 _89788 _89789 P f x) (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461563 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term177 _89769 _89788 _89789 P f x t) = (term168 _89769 _89788 _89789 P f x t).
Proof. exact (eq_refl (term177 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461564 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term178 _89769 _89788 _89789 P f x) = (term169 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461563 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461565 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461566 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term179 _89769 _89788 _89789 P f x) = (term170 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461565 _89769) (@lem3461564 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461568 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term180 _89769 _89788 _89789 P f x) = (term171 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461567) (@lem3461566 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461569 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461570 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term175 _89769 _89788 _89789 P x f) = (term172 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461568 _89769 _89788 _89789 P f x) (@lem3461569 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461572 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term181 _89769 _89788 _89789 P x f) = (term182 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461571) (@lem3461570 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461573 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term177 _89769 _89788 _89789 P f x t) = (term168 _89769 _89788 _89789 P f x t).
Proof. exact (eq_refl (term177 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461575 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term183 _89769 _89788 _89789 P f x t) = (term184 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461574) (@lem3461573 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461576 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461577 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term185 _89769 _89788 _89789 t P x f) = (term186 _89769 _89788 _89789 t P x f).
Proof. exact (MK_COMB (@lem3461575 _89769 _89788 _89789 P f x t) (@lem3461576 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461578 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term187 _89769 _89788 _89789 P x f) = (term188 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461577 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461579 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461580 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term176 _89769 _89788 _89789 P x f) = (term189 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461579 _89769) (@lem3461578 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461581 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term175 _89769 _89788 _89789 P x f) = (term176 _89769 _89788 _89789 P x f)) = ((term172 _89769 _89788 _89789 P x f) = (term189 _89769 _89788 _89789 P x f)).
Proof. exact (MK_COMB (@lem3461572 _89769 _89788 _89789 P x f) (@lem3461580 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461582 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term172 _89769 _89788 _89789 P x f) = (term189 _89769 _89788 _89789 P x f).
Proof. exact (EQ_MP (@lem3461581 _89769 _89788 _89789 P x f) (@lem3461562 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461584 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3461585 {_89789 : Type'} (P : _89789 -> Prop) (Q : Prop) : (term137 _89789 P Q) = (term138 _89789 P Q).
Proof. exact (@lem3461584 _89789 P Q). Qed.
Lemma lem3461586 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term190 _89769 _89788 _89789 t P x f) = (term191 _89769 _89788 _89789 t P x f).
Proof. exact (@lem3461585 _89789 (term167 _89769 _89788 _89789 P f x t) (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461587 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term192 _89769 _89788 _89789 P f x' t x) = (term166 _89769 _89788 _89789 P f x x' t).
Proof. exact (eq_refl (term192 _89769 _89788 _89789 P f x' t x)). Qed.
Lemma lem3461588 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term193 _89769 _89788 _89789 P f x t) = (term167 _89769 _89788 _89789 P f x t).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461587 _89769 _89788 _89789 P f x' x t)). Qed.
Lemma lem3461589 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461590 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term194 _89769 _89788 _89789 P f x t) = (term168 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461589 _89789) (@lem3461588 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461592 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term195 _89769 _89788 _89789 P f x t) = (term184 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461591) (@lem3461590 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461593 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461594 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term190 _89769 _89788 _89789 t P x f) = (term186 _89769 _89788 _89789 t P x f).
Proof. exact (MK_COMB (@lem3461592 _89769 _89788 _89789 P f x t) (@lem3461593 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461596 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term196 _89769 _89788 _89789 t P x f) = (term197 _89769 _89788 _89789 t P x f).
Proof. exact (MK_COMB (@lem3461595) (@lem3461594 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461597 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term192 _89769 _89788 _89789 P f x' t x) = (term166 _89769 _89788 _89789 P f x x' t).
Proof. exact (eq_refl (term192 _89769 _89788 _89789 P f x' t x)). Qed.
Lemma lem3461598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461599 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term198 _89769 _89788 _89789 P f x' t x) = (term199 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461598) (@lem3461597 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461600 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461601 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term200 _89769 _89788 _89789 t x P x' f) = (term201 _89769 _89788 _89789 x t P x' f).
Proof. exact (MK_COMB (@lem3461599 _89769 _89788 _89789 P f x x' t) (@lem3461600 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461602 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term202 _89769 _89788 _89789 t P x f) = (term203 _89769 _89788 _89789 t P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461601 _89769 _89788 _89789 x' t P x f)). Qed.
Lemma lem3461603 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461604 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term191 _89769 _89788 _89789 t P x f) = (term204 _89769 _89788 _89789 t P x f).
Proof. exact (MK_COMB (@lem3461603 _89789) (@lem3461602 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461605 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term190 _89769 _89788 _89789 t P x f) = (term191 _89769 _89788 _89789 t P x f)) = ((term186 _89769 _89788 _89789 t P x f) = (term204 _89769 _89788 _89789 t P x f)).
Proof. exact (MK_COMB (@lem3461596 _89769 _89788 _89789 t P x f) (@lem3461604 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461606 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term186 _89769 _89788 _89789 t P x f) = (term204 _89769 _89788 _89789 t P x f).
Proof. exact (EQ_MP (@lem3461605 _89769 _89788 _89789 t P x f) (@lem3461586 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3461609 {_89788 : Type'} (P : _89788 -> Prop) (Q : Prop) : (term137 _89788 P Q) = (term138 _89788 P Q).
Proof. exact (@lem3461608 _89788 P Q). Qed.
Lemma lem3461610 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term205 _89769 _89788 _89789 x t P x' f) = (term206 _89769 _89788 _89789 x t P x' f).
Proof. exact (@lem3461609 _89788 (term165 _89769 _89788 _89789 P f x x' t) (term95 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461611 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) (x' : _89769) (t : _89769 -> Prop) : (term207 _89769 _89788 _89789 P f x x' t y) = (term163 _89769 _89788 _89789 P f x y x' t).
Proof. exact (eq_refl (term207 _89769 _89788 _89789 P f x x' t y)). Qed.
Lemma lem3461612 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term208 _89769 _89788 _89789 P f x x' t) = (term165 _89769 _89788 _89789 P f x x' t).
Proof. exact (fun_ext (fun y : _89788 => @lem3461611 _89769 _89788 _89789 P f x y x' t)). Qed.
Lemma lem3461613 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461614 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term209 _89769 _89788 _89789 P f x x' t) = (term166 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461613 _89788) (@lem3461612 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461616 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term210 _89769 _89788 _89789 P f x x' t) = (term199 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461615) (@lem3461614 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461617 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461618 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term205 _89769 _89788 _89789 x t P x' f) = (term201 _89769 _89788 _89789 x t P x' f).
Proof. exact (MK_COMB (@lem3461616 _89769 _89788 _89789 P f x x' t) (@lem3461617 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461620 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term211 _89769 _89788 _89789 x t P x' f) = (term212 _89769 _89788 _89789 x t P x' f).
Proof. exact (MK_COMB (@lem3461619) (@lem3461618 _89769 _89788 _89789 x t P x' f)). Qed.
Lemma lem3461621 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) (x' : _89769) (t : _89769 -> Prop) : (term207 _89769 _89788 _89789 P f x x' t y) = (term163 _89769 _89788 _89789 P f x y x' t).
Proof. exact (eq_refl (term207 _89769 _89788 _89789 P f x x' t y)). Qed.
Lemma lem3461622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461623 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) (x' : _89769) (t : _89769 -> Prop) : (term213 _89769 _89788 _89789 P f x x' t y) = (term214 _89769 _89788 _89789 P f x y x' t).
Proof. exact (MK_COMB (@lem3461622) (@lem3461621 _89769 _89788 _89789 P f x y x' t)). Qed.
Lemma lem3461624 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term95 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461625 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term215 _89769 _89788 _89789 x t y P x' f) = (term216 _89769 _89788 _89789 x y t P x' f).
Proof. exact (MK_COMB (@lem3461623 _89769 _89788 _89789 P f x y x' t) (@lem3461624 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461626 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term217 _89769 _89788 _89789 x t P x' f) = (term218 _89769 _89788 _89789 x t P x' f).
Proof. exact (fun_ext (fun y : _89788 => @lem3461625 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461627 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461628 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term206 _89769 _89788 _89789 x t P x' f) = (term219 _89769 _89788 _89789 x t P x' f).
Proof. exact (MK_COMB (@lem3461627 _89788) (@lem3461626 _89769 _89788 _89789 x t P x' f)). Qed.
Lemma lem3461629 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : ((term205 _89769 _89788 _89789 x t P x' f) = (term206 _89769 _89788 _89789 x t P x' f)) = ((term201 _89769 _89788 _89789 x t P x' f) = (term219 _89769 _89788 _89789 x t P x' f)).
Proof. exact (MK_COMB (@lem3461620 _89769 _89788 _89789 x t P x' f) (@lem3461628 _89769 _89788 _89789 x t P x' f)). Qed.
Lemma lem3461630 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term201 _89769 _89788 _89789 x t P x' f) = (term219 _89769 _89788 _89789 x t P x' f).
Proof. exact (EQ_MP (@lem3461629 _89769 _89788 _89789 x t P x' f) (@lem3461610 _89769 _89788 _89789 x t P x' f)). Qed.
Lemma lem3461631 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term203 _89769 _89788 _89789 t P x f) = (term220 _89769 _89788 _89789 t P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461630 _89769 _89788 _89789 x' t P x f)). Qed.
Lemma lem3461632 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461633 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term204 _89769 _89788 _89789 t P x f) = (term221 _89769 _89788 _89789 t P x f).
Proof. exact (MK_COMB (@lem3461632 _89789) (@lem3461631 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461634 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term186 _89769 _89788 _89789 t P x f) = (term221 _89769 _89788 _89789 t P x f).
Proof. exact (TRANS (@lem3461606 _89769 _89788 _89789 t P x f) (@lem3461633 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461635 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term188 _89769 _89788 _89789 P x f) = (term222 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461634 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461636 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461637 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term189 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461636 _89769) (@lem3461635 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461638 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term172 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461582 _89769 _89788 _89789 P x f) (@lem3461637 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461639 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term99 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461558 _89769 _89788 _89789 P x f) (@lem3461638 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461640 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term107 _89769 _89788 _89789 P x f) = (term224 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461499 _89769 _89788 _89789 P x f) (@lem3461639 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461644 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3461645 {_89789 : Type'} (P : _89789 -> Prop) (Q : Prop) : (term225 _89789 P Q) = (term226 _89789 P Q).
Proof. exact (@lem3461644 _89789 P Q). Qed.
Lemma lem3461646 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term227 _89769 _89788 _89789 P x f) = (term228 _89769 _89788 _89789 P x f).
Proof. exact (@lem3461645 _89789 (term134 _89769 _89788 _89789 P x f) (term223 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461647 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term229 _89769 _89788 _89789 P x f x') = (term133 _89769 _89788 _89789 P x f x').
Proof. exact (eq_refl (term229 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461648 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term230 _89769 _89788 _89789 P x f) = (term134 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461647 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461649 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461650 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term231 _89769 _89788 _89789 P x f) = (term135 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461649 _89789) (@lem3461648 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461652 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term232 _89769 _89788 _89789 P x f) = (term136 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461651) (@lem3461650 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461653 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term223 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term223 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461654 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term227 _89769 _89788 _89789 P x f) = (term224 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461652 _89769 _89788 _89789 P x f) (@lem3461653 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461656 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term233 _89769 _89788 _89789 P x f) = (term234 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461655) (@lem3461654 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461657 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term229 _89769 _89788 _89789 P x f x') = (term133 _89769 _89788 _89789 P x f x').
Proof. exact (eq_refl (term229 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461659 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term235 _89769 _89788 _89789 P x f x') = (term236 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461658) (@lem3461657 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461660 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term223 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term223 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461661 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term237 _89769 _89788 _89789 x P x' f) = (term238 _89769 _89788 _89789 x P x' f).
Proof. exact (MK_COMB (@lem3461659 _89769 _89788 _89789 P x' f x) (@lem3461660 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461662 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term239 _89769 _89788 _89789 P x f) = (term240 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461661 _89769 _89788 _89789 x' P x f)). Qed.
Lemma lem3461663 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461664 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term228 _89769 _89788 _89789 P x f) = (term241 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461663 _89789) (@lem3461662 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461665 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : ((term227 _89769 _89788 _89789 P x f) = (term228 _89769 _89788 _89789 P x f)) = ((term224 _89769 _89788 _89789 P x f) = (term241 _89769 _89788 _89789 P x f)).
Proof. exact (MK_COMB (@lem3461656 _89769 _89788 _89789 P x f) (@lem3461664 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461666 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term224 _89769 _89788 _89789 P x f) = (term241 _89769 _89788 _89789 P x f).
Proof. exact (EQ_MP (@lem3461665 _89769 _89788 _89789 P x f) (@lem3461646 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461670 {A : Type'} (P : A -> Prop) (Q : Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3461671 {_89788 : Type'} (P : _89788 -> Prop) (Q : Prop) : (term225 _89788 P Q) = (term226 _89788 P Q).
Proof. exact (@lem3461670 _89788 P Q). Qed.
Lemma lem3461672 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term242 _89769 _89788 _89789 x P x' f) = (term243 _89769 _89788 _89789 x P x' f).
Proof. exact (@lem3461671 _89788 (term132 _89769 _89788 _89789 P x' f x) (term223 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461673 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term244 _89769 _89788 _89789 P x f x' y) = (term130 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term244 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461674 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term245 _89769 _89788 _89789 P x f x') = (term132 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3461673 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461675 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461676 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term246 _89769 _89788 _89789 P x f x') = (term133 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461675 _89788) (@lem3461674 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461678 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term247 _89769 _89788 _89789 P x f x') = (term236 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461677) (@lem3461676 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461679 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term223 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term223 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461680 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term242 _89769 _89788 _89789 x P x' f) = (term238 _89769 _89788 _89789 x P x' f).
Proof. exact (MK_COMB (@lem3461678 _89769 _89788 _89789 P x' f x) (@lem3461679 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461682 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term248 _89769 _89788 _89789 x P x' f) = (term249 _89769 _89788 _89789 x P x' f).
Proof. exact (MK_COMB (@lem3461681) (@lem3461680 _89769 _89788 _89789 x P x' f)). Qed.
Lemma lem3461683 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term244 _89769 _89788 _89789 P x f x' y) = (term130 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term244 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461685 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term250 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (MK_COMB (@lem3461684) (@lem3461683 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461686 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term223 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (eq_refl (term223 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461687 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term252 _89769 _89788 _89789 x y P x' f) = (term253 _89769 _89788 _89789 x y P x' f).
Proof. exact (MK_COMB (@lem3461685 _89769 _89788 _89789 P x' f x y) (@lem3461686 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461688 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term254 _89769 _89788 _89789 x P x' f) = (term255 _89769 _89788 _89789 x P x' f).
Proof. exact (fun_ext (fun y : _89788 => @lem3461687 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461689 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461690 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term243 _89769 _89788 _89789 x P x' f) = (term256 _89769 _89788 _89789 x P x' f).
Proof. exact (MK_COMB (@lem3461689 _89788) (@lem3461688 _89769 _89788 _89789 x P x' f)). Qed.
Lemma lem3461691 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : ((term242 _89769 _89788 _89789 x P x' f) = (term243 _89769 _89788 _89789 x P x' f)) = ((term238 _89769 _89788 _89789 x P x' f) = (term256 _89769 _89788 _89789 x P x' f)).
Proof. exact (MK_COMB (@lem3461682 _89769 _89788 _89789 x P x' f) (@lem3461690 _89769 _89788 _89789 x P x' f)). Qed.
Lemma lem3461692 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term238 _89769 _89788 _89789 x P x' f) = (term256 _89769 _89788 _89789 x P x' f).
Proof. exact (EQ_MP (@lem3461691 _89769 _89788 _89789 x P x' f) (@lem3461672 _89769 _89788 _89789 x P x' f)). Qed.
Lemma lem3461694 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3461695 {_89769 : Type'} (P : Prop) (Q : type686 _89769) : (term259 _89769 P Q) = (term260 _89769 P Q).
Proof. exact (@lem3461694 (_89769 -> Prop) P Q). Qed.
Lemma lem3461696 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term261 _89769 _89788 _89789 x y P x' f) = (term262 _89769 _89788 _89789 x y P x' f).
Proof. exact (@lem3461695 _89769 (term130 _89769 _89788 _89789 P x' f x y) (term222 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461697 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term263 _89769 _89788 _89789 P x f t) = (term221 _89769 _89788 _89789 t P x f).
Proof. exact (eq_refl (term263 _89769 _89788 _89789 P x f t)). Qed.
Lemma lem3461698 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term264 _89769 _89788 _89789 P x f) = (term222 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461697 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461699 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461700 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term265 _89769 _89788 _89789 P x f) = (term223 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461699 _89769) (@lem3461698 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461701 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term251 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term251 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461702 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term261 _89769 _89788 _89789 x y P x' f) = (term253 _89769 _89788 _89789 x y P x' f).
Proof. exact (MK_COMB (@lem3461701 _89769 _89788 _89789 P x' f x y) (@lem3461700 _89769 _89788 _89789 P x' f)). Qed.
Lemma lem3461703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461704 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term266 _89769 _89788 _89789 x y P x' f) = (term267 _89769 _89788 _89789 x y P x' f).
Proof. exact (MK_COMB (@lem3461703) (@lem3461702 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461705 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term263 _89769 _89788 _89789 P x f t) = (term221 _89769 _89788 _89789 t P x f).
Proof. exact (eq_refl (term263 _89769 _89788 _89789 P x f t)). Qed.
Lemma lem3461706 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term251 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term251 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461707 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term268 _89769 _89788 _89789 x y P x' f t) = (term269 _89769 _89788 _89789 x y t P x' f).
Proof. exact (MK_COMB (@lem3461706 _89769 _89788 _89789 P x' f x y) (@lem3461705 _89769 _89788 _89789 t P x' f)). Qed.
Lemma lem3461708 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term270 _89769 _89788 _89789 x y P x' f) = (term271 _89769 _89788 _89789 x y P x' f).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461707 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461709 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461710 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term262 _89769 _89788 _89789 x y P x' f) = (term272 _89769 _89788 _89789 x y P x' f).
Proof. exact (MK_COMB (@lem3461709 _89769) (@lem3461708 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461711 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : ((term261 _89769 _89788 _89789 x y P x' f) = (term262 _89769 _89788 _89789 x y P x' f)) = ((term253 _89769 _89788 _89789 x y P x' f) = (term272 _89769 _89788 _89789 x y P x' f)).
Proof. exact (MK_COMB (@lem3461704 _89769 _89788 _89789 x y P x' f) (@lem3461710 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461712 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term253 _89769 _89788 _89789 x y P x' f) = (term272 _89769 _89788 _89789 x y P x' f).
Proof. exact (EQ_MP (@lem3461711 _89769 _89788 _89789 x y P x' f) (@lem3461696 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461714 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3461715 {_89789 : Type'} (P : Prop) (Q : _89789 -> Prop) : (term257 _89789 P Q) = (term258 _89789 P Q).
Proof. exact (@lem3461714 _89789 P Q). Qed.
Lemma lem3461716 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term273 _89769 _89788 _89789 x y t P x' f) = (term274 _89769 _89788 _89789 x y t P x' f).
Proof. exact (@lem3461715 _89789 (term130 _89769 _89788 _89789 P x' f x y) (term220 _89769 _89788 _89789 t P x' f)). Qed.
Lemma lem3461717 {_89769 _89788 _89789 : Type'} (x : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term275 _89769 _89788 _89789 t P x' f x) = (term219 _89769 _89788 _89789 x t P x' f).
Proof. exact (eq_refl (term275 _89769 _89788 _89789 t P x' f x)). Qed.
Lemma lem3461718 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term276 _89769 _89788 _89789 t P x f) = (term220 _89769 _89788 _89789 t P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461717 _89769 _89788 _89789 x' t P x f)). Qed.
Lemma lem3461719 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461720 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term277 _89769 _89788 _89789 t P x f) = (term221 _89769 _89788 _89789 t P x f).
Proof. exact (MK_COMB (@lem3461719 _89789) (@lem3461718 _89769 _89788 _89789 t P x f)). Qed.
Lemma lem3461721 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term251 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term251 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461722 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term273 _89769 _89788 _89789 x y t P x' f) = (term269 _89769 _89788 _89789 x y t P x' f).
Proof. exact (MK_COMB (@lem3461721 _89769 _89788 _89789 P x' f x y) (@lem3461720 _89769 _89788 _89789 t P x' f)). Qed.
Lemma lem3461723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461724 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term278 _89769 _89788 _89789 x y t P x' f) = (term279 _89769 _89788 _89789 x y t P x' f).
Proof. exact (MK_COMB (@lem3461723) (@lem3461722 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461725 {_89769 _89788 _89789 : Type'} (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term275 _89769 _89788 _89789 t P x f x') = (term219 _89769 _89788 _89789 x' t P x f).
Proof. exact (eq_refl (term275 _89769 _89788 _89789 t P x f x')). Qed.
Lemma lem3461726 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term251 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term251 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461727 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term280 _89769 _89788 _89789 x y t P x'' f x') = (term281 _89769 _89788 _89789 x y x' t P x'' f).
Proof. exact (MK_COMB (@lem3461726 _89769 _89788 _89789 P x'' f x y) (@lem3461725 _89769 _89788 _89789 x' t P x'' f)). Qed.
Lemma lem3461728 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term282 _89769 _89788 _89789 x y t P x' f) = (term283 _89769 _89788 _89789 x y t P x' f).
Proof. exact (fun_ext (fun x'' : _89789 => @lem3461727 _89769 _89788 _89789 x y x'' t P x' f)). Qed.
Lemma lem3461729 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461730 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term274 _89769 _89788 _89789 x y t P x' f) = (term284 _89769 _89788 _89789 x y t P x' f).
Proof. exact (MK_COMB (@lem3461729 _89789) (@lem3461728 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461731 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : ((term273 _89769 _89788 _89789 x y t P x' f) = (term274 _89769 _89788 _89789 x y t P x' f)) = ((term269 _89769 _89788 _89789 x y t P x' f) = (term284 _89769 _89788 _89789 x y t P x' f)).
Proof. exact (MK_COMB (@lem3461724 _89769 _89788 _89789 x y t P x' f) (@lem3461730 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461732 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term269 _89769 _89788 _89789 x y t P x' f) = (term284 _89769 _89788 _89789 x y t P x' f).
Proof. exact (EQ_MP (@lem3461731 _89769 _89788 _89789 x y t P x' f) (@lem3461716 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461734 {A : Type'} (P : Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3461735 {_89788 : Type'} (P : Prop) (Q : _89788 -> Prop) : (term257 _89788 P Q) = (term258 _89788 P Q).
Proof. exact (@lem3461734 _89788 P Q). Qed.
Lemma lem3461736 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term285 _89769 _89788 _89789 x y x' t P x'' f) = (term286 _89769 _89788 _89789 x y x' t P x'' f).
Proof. exact (@lem3461735 _89788 (term130 _89769 _89788 _89789 P x'' f x y) (term218 _89769 _89788 _89789 x' t P x'' f)). Qed.
Lemma lem3461737 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term287 _89769 _89788 _89789 x' t P x f y) = (term216 _89769 _89788 _89789 x' y t P x f).
Proof. exact (eq_refl (term287 _89769 _89788 _89789 x' t P x f y)). Qed.
Lemma lem3461738 {_89769 _89788 _89789 : Type'} (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term288 _89769 _89788 _89789 x' t P x f) = (term218 _89769 _89788 _89789 x' t P x f).
Proof. exact (fun_ext (fun y : _89788 => @lem3461737 _89769 _89788 _89789 x' y t P x f)). Qed.
Lemma lem3461739 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461740 {_89769 _89788 _89789 : Type'} (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term289 _89769 _89788 _89789 x' t P x f) = (term219 _89769 _89788 _89789 x' t P x f).
Proof. exact (MK_COMB (@lem3461739 _89788) (@lem3461738 _89769 _89788 _89789 x' t P x f)). Qed.
Lemma lem3461741 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term251 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term251 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461742 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term285 _89769 _89788 _89789 x y x' t P x'' f) = (term281 _89769 _89788 _89789 x y x' t P x'' f).
Proof. exact (MK_COMB (@lem3461741 _89769 _89788 _89789 P x'' f x y) (@lem3461740 _89769 _89788 _89789 x' t P x'' f)). Qed.
Lemma lem3461743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461744 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term290 _89769 _89788 _89789 x y x' t P x'' f) = (term291 _89769 _89788 _89789 x y x' t P x'' f).
Proof. exact (MK_COMB (@lem3461743) (@lem3461742 _89769 _89788 _89789 x y x' t P x'' f)). Qed.
Lemma lem3461745 {_89769 _89788 _89789 : Type'} (x' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term287 _89769 _89788 _89789 x' t P x f y') = (term216 _89769 _89788 _89789 x' y' t P x f).
Proof. exact (eq_refl (term287 _89769 _89788 _89789 x' t P x f y')). Qed.
Lemma lem3461746 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term251 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term251 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461747 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term292 _89769 _89788 _89789 x y x' t P x'' f y') = (term293 _89769 _89788 _89789 x y x' y' t P x'' f).
Proof. exact (MK_COMB (@lem3461746 _89769 _89788 _89789 P x'' f x y) (@lem3461745 _89769 _89788 _89789 x' y' t P x'' f)). Qed.
Lemma lem3461748 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term294 _89769 _89788 _89789 x y x' t P x'' f) = (term295 _89769 _89788 _89789 x y x' t P x'' f).
Proof. exact (fun_ext (fun y' : _89788 => @lem3461747 _89769 _89788 _89789 x y x' y' t P x'' f)). Qed.
Lemma lem3461749 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461750 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term286 _89769 _89788 _89789 x y x' t P x'' f) = (term296 _89769 _89788 _89789 x y x' t P x'' f).
Proof. exact (MK_COMB (@lem3461749 _89788) (@lem3461748 _89769 _89788 _89789 x y x' t P x'' f)). Qed.
Lemma lem3461751 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : ((term285 _89769 _89788 _89789 x y x' t P x'' f) = (term286 _89769 _89788 _89789 x y x' t P x'' f)) = ((term281 _89769 _89788 _89789 x y x' t P x'' f) = (term296 _89769 _89788 _89789 x y x' t P x'' f)).
Proof. exact (MK_COMB (@lem3461744 _89769 _89788 _89789 x y x' t P x'' f) (@lem3461750 _89769 _89788 _89789 x y x' t P x'' f)). Qed.
Lemma lem3461752 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (x' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x'' : _89769) (f : type1517 _89769 _89788 _89789) : (term281 _89769 _89788 _89789 x y x' t P x'' f) = (term296 _89769 _89788 _89789 x y x' t P x'' f).
Proof. exact (EQ_MP (@lem3461751 _89769 _89788 _89789 x y x' t P x'' f) (@lem3461736 _89769 _89788 _89789 x y x' t P x'' f)). Qed.
Lemma lem3461753 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term283 _89769 _89788 _89789 x y t P x' f) = (term297 _89769 _89788 _89789 x y t P x' f).
Proof. exact (fun_ext (fun x'' : _89789 => @lem3461752 _89769 _89788 _89789 x y x'' t P x' f)). Qed.
Lemma lem3461754 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461755 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term284 _89769 _89788 _89789 x y t P x' f) = (term298 _89769 _89788 _89789 x y t P x' f).
Proof. exact (MK_COMB (@lem3461754 _89789) (@lem3461753 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461756 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term269 _89769 _89788 _89789 x y t P x' f) = (term298 _89769 _89788 _89789 x y t P x' f).
Proof. exact (TRANS (@lem3461732 _89769 _89788 _89789 x y t P x' f) (@lem3461755 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461757 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term271 _89769 _89788 _89789 x y P x' f) = (term299 _89769 _89788 _89789 x y P x' f).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461756 _89769 _89788 _89789 x y t P x' f)). Qed.
Lemma lem3461758 {_89769 : Type'} : (@ex (_89769 -> Prop)) = (@ex (_89769 -> Prop)).
Proof. exact (eq_refl (@ex (_89769 -> Prop))). Qed.
Lemma lem3461759 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term272 _89769 _89788 _89789 x y P x' f) = (term300 _89769 _89788 _89789 x y P x' f).
Proof. exact (MK_COMB (@lem3461758 _89769) (@lem3461757 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461760 {_89769 _89788 _89789 : Type'} (x : _89789) (y : _89788) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term253 _89769 _89788 _89789 x y P x' f) = (term300 _89769 _89788 _89789 x y P x' f).
Proof. exact (TRANS (@lem3461712 _89769 _89788 _89789 x y P x' f) (@lem3461759 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461761 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term255 _89769 _89788 _89789 x P x' f) = (term301 _89769 _89788 _89789 x P x' f).
Proof. exact (fun_ext (fun y : _89788 => @lem3461760 _89769 _89788 _89789 x y P x' f)). Qed.
Lemma lem3461762 {_89788 : Type'} : (@ex _89788) = (@ex _89788).
Proof. exact (eq_refl (@ex _89788)). Qed.
Lemma lem3461763 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term256 _89769 _89788 _89789 x P x' f) = (term302 _89769 _89788 _89789 x P x' f).
Proof. exact (MK_COMB (@lem3461762 _89788) (@lem3461761 _89769 _89788 _89789 x P x' f)). Qed.
Lemma lem3461764 {_89769 _89788 _89789 : Type'} (x : _89789) (P : type1470 _89788 _89789) (x' : _89769) (f : type1517 _89769 _89788 _89789) : (term238 _89769 _89788 _89789 x P x' f) = (term302 _89769 _89788 _89789 x P x' f).
Proof. exact (TRANS (@lem3461692 _89769 _89788 _89789 x P x' f) (@lem3461763 _89769 _89788 _89789 x P x' f)). Qed.
Lemma lem3461765 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term240 _89769 _89788 _89789 P x f) = (term303 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461764 _89769 _89788 _89789 x' P x f)). Qed.
Lemma lem3461766 {_89789 : Type'} : (@ex _89789) = (@ex _89789).
Proof. exact (eq_refl (@ex _89789)). Qed.
Lemma lem3461767 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term241 _89769 _89788 _89789 P x f) = (term304 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461766 _89789) (@lem3461765 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461768 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term224 _89769 _89788 _89789 P x f) = (term304 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461666 _89769 _89788 _89789 P x f) (@lem3461767 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461770 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term107 _89769 _89788 _89789 P x f) = (term304 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461640 _89769 _89788 _89789 P x f) (@lem3461768 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461771 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term34 _89769 _89788 _89789 P x f) = (term304 _89769 _89788 _89789 P x f).
Proof. exact (TRANS (@lem3461148 _89769 _89788 _89789 P x f) (@lem3461770 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461772 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term34 _89769 _89788 _89789 P x f) : term304 _89769 _89788 _89789 P x f.
Proof. exact (EQ_MP (@lem3461771 _89769 _89788 _89789 P x f) (@lem3461034 _89769 _89788 _89789 P x f h1)). Qed.
Lemma lem3461773 {_89769 _89788 _89789 : Type'} (x' : _89789) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term302 _89769 _89788 _89789 x' P x f) : term302 _89769 _89788 _89789 x' P x f.
Proof. exact (h1). Qed.
Lemma lem3461774 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term300 _89769 _89788 _89789 x' y P x f) : term300 _89769 _89788 _89789 x' y P x f.
Proof. exact (h1). Qed.
Lemma lem3461775 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term298 _89769 _89788 _89789 x' y t P x f) : term298 _89769 _89788 _89789 x' y t P x f.
Proof. exact (h1). Qed.
Lemma lem3461776 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term296 _89769 _89788 _89789 x' y x'' t P x f) : term296 _89769 _89788 _89789 x' y x'' t P x f.
Proof. exact (h1). Qed.
Lemma lem3461777 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term293 _89769 _89788 _89789 x' y x'' y' t P x f) : term293 _89769 _89788 _89789 x' y x'' y' t P x f.
Proof. exact (h1). Qed.
Lemma lem3461796 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term75 _89769 _89788 _89789 P x f x' y) = (term75 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term75 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461797 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term85 _89769 _89788 _89789 P x f x') = (term85 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3461796 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461798 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3461799 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term86 _89769 _89788 _89789 P x f x') = (term86 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3461798 _89788) (@lem3461797 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461800 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term94 _89769 _89788 _89789 P x f) = (term94 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461799 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3461801 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461802 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3461801 _89789) (@lem3461800 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461831 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) (x : _89769) (t : _89769 -> Prop) : (term214 _89769 _89788 _89789 P f x'' y' x t) = (term214 _89769 _89788 _89789 P f x'' y' x t).
Proof. exact (eq_refl (term214 _89769 _89788 _89789 P f x'' y' x t)). Qed.
Lemma lem3461832 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term216 _89769 _89788 _89789 x'' y' t P x f) = (term216 _89769 _89788 _89789 x'' y' t P x f).
Proof. exact (MK_COMB (@lem3461831 _89769 _89788 _89789 P f x'' y' x t) (@lem3461802 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3461851 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term73 _89769 _89788 _89789 P x f x' y) = (term73 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term73 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461856 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3461877 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term36 _89769 _89788 _89789 P t f x y) = (term36 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term36 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461878 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term44 _89769 _89788 _89789 P t f x) = (term44 _89769 _89788 _89789 P t f x).
Proof. exact (fun_ext (fun y : _89788 => @lem3461877 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461879 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3461880 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term45 _89769 _89788 _89789 P t f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461879 _89788) (@lem3461878 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461881 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term51 _89769 _89788 _89789 P t f) = (term51 _89769 _89788 _89789 P t f).
Proof. exact (fun_ext (fun x : _89789 => @lem3461880 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461882 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461883 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term52 _89769 _89788 _89789 P t f) = (term52 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461882 _89789) (@lem3461881 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461885 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term58 _89769 _89788 _89789 P t f) = (term58 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461884) (@lem3461883 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461886 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term60 _89769 _89788 _89789 P f x t) = (term60 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461885 _89769 _89788 _89789 P t f) (@lem3461856 _89769 x t)). Qed.
Lemma lem3461887 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term70 _89769 _89788 _89789 P f x) = (term70 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461886 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461888 {_89769 : Type'} : (@all (_89769 -> Prop)) = (@all (_89769 -> Prop)).
Proof. exact (eq_refl (@all (_89769 -> Prop))). Qed.
Lemma lem3461889 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term71 _89769 _89788 _89789 P f x) = (term71 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461888 _89769) (@lem3461887 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3461891 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term101 _89769 _89788 _89789 P f x) = (term101 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461890) (@lem3461889 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461892 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term130 _89769 _89788 _89789 P x f x' y) = (term130 _89769 _89788 _89789 P x f x' y).
Proof. exact (MK_COMB (@lem3461891 _89769 _89788 _89789 P f x) (@lem3461851 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461894 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term251 _89769 _89788 _89789 P x f x' y) = (term251 _89769 _89788 _89789 P x f x' y).
Proof. exact (MK_COMB (@lem3461893) (@lem3461892 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3461895 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term293 _89769 _89788 _89789 x' y x'' y' t P x f) = (term293 _89769 _89788 _89789 x' y x'' y' t P x f).
Proof. exact (MK_COMB (@lem3461894 _89769 _89788 _89789 P x f x' y) (@lem3461832 _89769 _89788 _89789 x'' y' t P x f)). Qed.
Lemma lem3461896 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term293 _89769 _89788 _89789 x' y x'' y' t P x f) : term293 _89769 _89788 _89789 x' y x'' y' t P x f.
Proof. exact (EQ_MP (@lem3461895 _89769 _89788 _89789 x' y x'' y' t P x f) (@lem3461777 _89769 _89788 _89789 x' y x'' y' t P x f h1)). Qed.
Lemma lem3461897 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term130 _89769 _89788 _89789 P x f x' y.
Proof. exact (h1). Qed.
Lemma lem3461898 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term216 _89769 _89788 _89789 x'' y' t P x f.
Proof. exact (h1). Qed.
Lemma lem3461899 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term73 _89769 _89788 _89789 P x f x' y.
Proof. exact (proj2 (@lem3461897 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3461900 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term71 _89769 _89788 _89789 P f x.
Proof. exact (proj1 (@lem3461897 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3461903 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term95 _89769 _89788 _89789 P x f.
Proof. exact (proj2 (@lem3461898 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3461904 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term163 _89769 _89788 _89789 P f x'' y' x t.
Proof. exact (proj1 (@lem3461898 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3461906 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term22 _89769 _89788 _89789 P t f x'' y'.
Proof. exact (proj1 (@lem3461904 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3461910 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3461911 {_89789 : Type'} (P : _89789 -> Prop) (Q : Prop) : (term305 _89789 P Q) = (term306 _89789 P Q).
Proof. exact (@lem3461910 _89789 P Q). Qed.
Lemma lem3461912 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term307 _89769 _89788 _89789 P f x t) = (term308 _89769 _89788 _89789 P f x t).
Proof. exact (@lem3461911 _89789 (term51 _89769 _89788 _89789 P t f) (@IN _89769 x t)). Qed.
Lemma lem3461913 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term309 _89769 _89788 _89789 P t f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (eq_refl (term309 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461914 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term310 _89769 _89788 _89789 P t f) = (term51 _89769 _89788 _89789 P t f).
Proof. exact (fun_ext (fun x : _89789 => @lem3461913 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461915 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461916 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term311 _89769 _89788 _89789 P t f) = (term52 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461915 _89789) (@lem3461914 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461918 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) : (term312 _89769 _89788 _89789 P t f) = (term58 _89769 _89788 _89789 P t f).
Proof. exact (MK_COMB (@lem3461917) (@lem3461916 _89769 _89788 _89789 P t f)). Qed.
Lemma lem3461919 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3461920 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term307 _89769 _89788 _89789 P f x t) = (term60 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461918 _89769 _89788 _89789 P t f) (@lem3461919 _89769 x t)). Qed.
Lemma lem3461921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461922 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term313 _89769 _89788 _89789 P f x t) = (term314 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461921) (@lem3461920 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461923 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term309 _89769 _89788 _89789 P t f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (eq_refl (term309 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461925 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term315 _89769 _89788 _89789 P t f x) = (term316 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461924) (@lem3461923 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461926 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3461927 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term317 _89769 _89788 _89789 P f x x' t) = (term318 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461925 _89769 _89788 _89789 P t f x) (@lem3461926 _89769 x' t)). Qed.
Lemma lem3461928 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term319 _89769 _89788 _89789 P f x t) = (term320 _89769 _89788 _89789 P f x t).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461927 _89769 _89788 _89789 P f x' x t)). Qed.
Lemma lem3461929 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461930 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term308 _89769 _89788 _89789 P f x t) = (term321 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461929 _89789) (@lem3461928 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461931 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : ((term307 _89769 _89788 _89789 P f x t) = (term308 _89769 _89788 _89789 P f x t)) = ((term60 _89769 _89788 _89789 P f x t) = (term321 _89769 _89788 _89789 P f x t)).
Proof. exact (MK_COMB (@lem3461922 _89769 _89788 _89789 P f x t) (@lem3461930 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461932 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term60 _89769 _89788 _89789 P f x t) = (term321 _89769 _89788 _89789 P f x t).
Proof. exact (EQ_MP (@lem3461931 _89769 _89788 _89789 P f x t) (@lem3461912 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461934 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3461935 {_89788 : Type'} (P : _89788 -> Prop) (Q : Prop) : (term305 _89788 P Q) = (term306 _89788 P Q).
Proof. exact (@lem3461934 _89788 P Q). Qed.
Lemma lem3461936 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term322 _89769 _89788 _89789 P f x x' t) = (term323 _89769 _89788 _89789 P f x x' t).
Proof. exact (@lem3461935 _89788 (term44 _89769 _89788 _89789 P t f x) (@IN _89769 x' t)). Qed.
Lemma lem3461937 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term324 _89769 _89788 _89789 P t f x y) = (term36 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term324 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461938 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term325 _89769 _89788 _89789 P t f x) = (term44 _89769 _89788 _89789 P t f x).
Proof. exact (fun_ext (fun y : _89788 => @lem3461937 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461939 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3461940 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term326 _89769 _89788 _89789 P t f x) = (term45 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461939 _89788) (@lem3461938 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461942 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) : (term327 _89769 _89788 _89789 P t f x) = (term316 _89769 _89788 _89789 P t f x).
Proof. exact (MK_COMB (@lem3461941) (@lem3461940 _89769 _89788 _89789 P t f x)). Qed.
Lemma lem3461943 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3461944 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term322 _89769 _89788 _89789 P f x x' t) = (term318 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461942 _89769 _89788 _89789 P t f x) (@lem3461943 _89769 x' t)). Qed.
Lemma lem3461945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3461946 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term328 _89769 _89788 _89789 P f x x' t) = (term329 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461945) (@lem3461944 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461947 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term324 _89769 _89788 _89789 P t f x y) = (term36 _89769 _89788 _89789 P t f x y).
Proof. exact (eq_refl (term324 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3461949 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (t : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) : (term330 _89769 _89788 _89789 P t f x y) = (term331 _89769 _89788 _89789 P t f x y).
Proof. exact (MK_COMB (@lem3461948) (@lem3461947 _89769 _89788 _89789 P t f x y)). Qed.
Lemma lem3461950 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (@IN _89769 x t) = (@IN _89769 x t).
Proof. exact (eq_refl (@IN _89769 x t)). Qed.
Lemma lem3461951 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) (x' : _89769) (t : _89769 -> Prop) : (term332 _89769 _89788 _89789 P f x y x' t) = (term333 _89769 _89788 _89789 P f x y x' t).
Proof. exact (MK_COMB (@lem3461949 _89769 _89788 _89789 P t f x y) (@lem3461950 _89769 x' t)). Qed.
Lemma lem3461952 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term334 _89769 _89788 _89789 P f x x' t) = (term335 _89769 _89788 _89789 P f x x' t).
Proof. exact (fun_ext (fun y : _89788 => @lem3461951 _89769 _89788 _89789 P f x y x' t)). Qed.
Lemma lem3461953 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3461954 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term323 _89769 _89788 _89789 P f x x' t) = (term336 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461953 _89788) (@lem3461952 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461955 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : ((term322 _89769 _89788 _89789 P f x x' t) = (term323 _89769 _89788 _89789 P f x x' t)) = ((term318 _89769 _89788 _89789 P f x x' t) = (term336 _89769 _89788 _89789 P f x x' t)).
Proof. exact (MK_COMB (@lem3461946 _89769 _89788 _89789 P f x x' t) (@lem3461954 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461956 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term318 _89769 _89788 _89789 P f x x' t) = (term336 _89769 _89788 _89789 P f x x' t).
Proof. exact (EQ_MP (@lem3461955 _89769 _89788 _89789 P f x x' t) (@lem3461936 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461957 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term320 _89769 _89788 _89789 P f x t) = (term337 _89769 _89788 _89789 P f x t).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461956 _89769 _89788 _89789 P f x' x t)). Qed.
Lemma lem3461958 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461959 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term321 _89769 _89788 _89789 P f x t) = (term338 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461958 _89789) (@lem3461957 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461960 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term60 _89769 _89788 _89789 P f x t) = (term338 _89769 _89788 _89789 P f x t).
Proof. exact (TRANS (@lem3461932 _89769 _89788 _89789 P f x t) (@lem3461959 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461961 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term70 _89769 _89788 _89789 P f x) = (term339 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461960 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461962 {_89769 : Type'} : (@all (_89769 -> Prop)) = (@all (_89769 -> Prop)).
Proof. exact (eq_refl (@all (_89769 -> Prop))). Qed.
Lemma lem3461963 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term71 _89769 _89788 _89789 P f x) = (term340 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461962 _89769) (@lem3461961 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461976 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (y : _89788) (x' : _89769) (t : _89769 -> Prop) : (term333 _89769 _89788 _89789 P f x y x' t) = (term333 _89769 _89788 _89789 P f x y x' t).
Proof. exact (eq_refl (term333 _89769 _89788 _89789 P f x y x' t)). Qed.
Lemma lem3461977 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term335 _89769 _89788 _89789 P f x x' t) = (term335 _89769 _89788 _89789 P f x x' t).
Proof. exact (fun_ext (fun y : _89788 => @lem3461976 _89769 _89788 _89789 P f x y x' t)). Qed.
Lemma lem3461978 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3461979 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89789) (x' : _89769) (t : _89769 -> Prop) : (term336 _89769 _89788 _89789 P f x x' t) = (term336 _89769 _89788 _89789 P f x x' t).
Proof. exact (MK_COMB (@lem3461978 _89788) (@lem3461977 _89769 _89788 _89789 P f x x' t)). Qed.
Lemma lem3461980 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term337 _89769 _89788 _89789 P f x t) = (term337 _89769 _89788 _89789 P f x t).
Proof. exact (fun_ext (fun x' : _89789 => @lem3461979 _89769 _89788 _89789 P f x' x t)). Qed.
Lemma lem3461981 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3461982 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (t : _89769 -> Prop) : (term338 _89769 _89788 _89789 P f x t) = (term338 _89769 _89788 _89789 P f x t).
Proof. exact (MK_COMB (@lem3461981 _89789) (@lem3461980 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461983 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term339 _89769 _89788 _89789 P f x) = (term339 _89769 _89788 _89789 P f x).
Proof. exact (fun_ext (fun t : _89769 -> Prop => @lem3461982 _89769 _89788 _89789 P f x t)). Qed.
Lemma lem3461984 {_89769 : Type'} : (@all (_89769 -> Prop)) = (@all (_89769 -> Prop)).
Proof. exact (eq_refl (@all (_89769 -> Prop))). Qed.
Lemma lem3461985 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term340 _89769 _89788 _89789 P f x) = (term340 _89769 _89788 _89789 P f x).
Proof. exact (MK_COMB (@lem3461984 _89769) (@lem3461983 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461986 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) : (term71 _89769 _89788 _89789 P f x) = (term340 _89769 _89788 _89789 P f x).
Proof. exact (TRANS (@lem3461963 _89769 _89788 _89789 P f x) (@lem3461985 _89769 _89788 _89789 P f x)). Qed.
Lemma lem3461987 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term340 _89769 _89788 _89789 P f x.
Proof. exact (EQ_MP (@lem3461986 _89769 _89788 _89789 P f x) (@lem3461900 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462003 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term75 _89769 _89788 _89789 P x f x' y) = (term75 _89769 _89788 _89789 P x f x' y).
Proof. exact (eq_refl (term75 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3462004 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term85 _89769 _89788 _89789 P x f x') = (term85 _89769 _89788 _89789 P x f x').
Proof. exact (fun_ext (fun y : _89788 => @lem3462003 _89769 _89788 _89789 P x f x' y)). Qed.
Lemma lem3462005 {_89788 : Type'} : (@all _89788) = (@all _89788).
Proof. exact (eq_refl (@all _89788)). Qed.
Lemma lem3462006 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) : (term86 _89769 _89788 _89789 P x f x') = (term86 _89769 _89788 _89789 P x f x').
Proof. exact (MK_COMB (@lem3462005 _89788) (@lem3462004 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3462007 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term94 _89769 _89788 _89789 P x f) = (term94 _89769 _89788 _89789 P x f).
Proof. exact (fun_ext (fun x' : _89789 => @lem3462006 _89769 _89788 _89789 P x f x')). Qed.
Lemma lem3462008 {_89789 : Type'} : (@all _89789) = (@all _89789).
Proof. exact (eq_refl (@all _89789)). Qed.
Lemma lem3462010 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term95 _89769 _89788 _89789 P x f) = (term95 _89769 _89788 _89789 P x f).
Proof. exact (MK_COMB (@lem3462008 _89789) (@lem3462007 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3462011 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term95 _89769 _89788 _89789 P x f.
Proof. exact (EQ_MP (@lem3462010 _89769 _89788 _89789 P x f) (@lem3461903 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462024 {_89769 _89788 _89789 : Type'} (_36539 : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term341 _89769 _89788 _89789 P f x _36539.
Proof. exact (@lem3461987 _89769 _89788 _89789 P x f x' y h1 _36539). Qed.
Lemma lem3462025 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (x : _89769) (_36539 : _89769 -> Prop) : (term341 _89769 _89788 _89789 P f x _36539) = (term338 _89769 _89788 _89789 P f x _36539).
Proof. exact (eq_refl (term341 _89769 _89788 _89789 P f x _36539)). Qed.
Lemma lem3462026 {_89769 _89788 _89789 : Type'} (_36539 : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term338 _89769 _89788 _89789 P f x _36539.
Proof. exact (EQ_MP (@lem3462025 _89769 _89788 _89789 P f x _36539) (@lem3462024 _89769 _89788 _89789 _36539 P x f x' y h1)). Qed.
Lemma lem3462027 {_89769 _89788 _89789 : Type'} (_36539 : _89769 -> Prop) (_36540 : _89789) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term342 _89769 _89788 _89789 P f x _36539 _36540.
Proof. exact (@lem3462026 _89769 _89788 _89789 _36539 P x f x' y h1 _36540). Qed.
Lemma lem3462028 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (x : _89769) (_36539 : _89769 -> Prop) : (term342 _89769 _89788 _89789 P f x _36539 _36540) = (term336 _89769 _89788 _89789 P f _36540 x _36539).
Proof. exact (eq_refl (term342 _89769 _89788 _89789 P f x _36539 _36540)). Qed.
Lemma lem3462029 {_89769 _89788 _89789 : Type'} (_36540 : _89789) (_36539 : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term336 _89769 _89788 _89789 P f _36540 x _36539.
Proof. exact (EQ_MP (@lem3462028 _89769 _89788 _89789 P f _36540 x _36539) (@lem3462027 _89769 _89788 _89789 _36539 _36540 P x f x' y h1)). Qed.
Lemma lem3462030 {_89769 _89788 _89789 : Type'} (_36540 : _89789) (_36539 : _89769 -> Prop) (_36541 : _89788) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term343 _89769 _89788 _89789 P f _36540 x _36539 _36541.
Proof. exact (@lem3462029 _89769 _89788 _89789 _36540 _36539 P x f x' y h1 _36541). Qed.
Lemma lem3462031 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) (x : _89769) (_36539 : _89769 -> Prop) : (term343 _89769 _89788 _89789 P f _36540 x _36539 _36541) = (term333 _89769 _89788 _89789 P f _36540 _36541 x _36539).
Proof. exact (eq_refl (term343 _89769 _89788 _89789 P f _36540 x _36539 _36541)). Qed.
Lemma lem3462032 {_89769 _89788 _89789 : Type'} (_36540 : _89789) (_36541 : _89788) (_36539 : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term333 _89769 _89788 _89789 P f _36540 _36541 x _36539.
Proof. exact (EQ_MP (@lem3462031 _89769 _89788 _89789 P f _36540 _36541 x _36539) (@lem3462030 _89769 _89788 _89789 _36540 _36539 _36541 P x f x' y h1)). Qed.
Lemma lem3462033 {_89769 _89788 _89789 : Type'} (_36542 : _89789) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term344 _89769 _89788 _89789 P x f _36542.
Proof. exact (@lem3462011 _89769 _89788 _89789 x'' y' t P x f h1 _36542). Qed.
Lemma lem3462034 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (_36542 : _89789) : (term344 _89769 _89788 _89789 P x f _36542) = (term86 _89769 _89788 _89789 P x f _36542).
Proof. exact (eq_refl (term344 _89769 _89788 _89789 P x f _36542)). Qed.
Lemma lem3462035 {_89769 _89788 _89789 : Type'} (_36542 : _89789) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term86 _89769 _89788 _89789 P x f _36542.
Proof. exact (EQ_MP (@lem3462034 _89769 _89788 _89789 P x f _36542) (@lem3462033 _89769 _89788 _89789 _36542 x'' y' t P x f h1)). Qed.
Lemma lem3462036 {_89769 _89788 _89789 : Type'} (_36542 : _89789) (_36543 : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term345 _89769 _89788 _89789 P x f _36542 _36543.
Proof. exact (@lem3462035 _89769 _89788 _89789 _36542 x'' y' t P x f h1 _36543). Qed.
Lemma lem3462037 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term345 _89769 _89788 _89789 P x f _36542 _36543) = (term75 _89769 _89788 _89789 P x f _36542 _36543).
Proof. exact (eq_refl (term345 _89769 _89788 _89789 P x f _36542 _36543)). Qed.
Lemma lem3462049 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) (x : _89769) (_36539 : _89769 -> Prop) : (term333 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term346 _89769 _89788 _89789 P f _36540 _36541 x _36539).
Proof. exact (@lem3458986 (term347 _89788 _89789 P _36540 _36541) (term348 _89769 _89788 _89789 _36539 f _36540 _36541) (@IN _89769 x _36539)). Qed.
Lemma lem3462050 {_89769 _89788 _89789 : Type'} (_36540 : _89789) (_36541 : _89788) (_36539 : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term346 _89769 _89788 _89789 P f _36540 _36541 x _36539.
Proof. exact (EQ_MP (@lem3462049 _89769 _89788 _89789 P f _36540 _36541 x _36539) (@lem3462032 _89769 _89788 _89789 _36540 _36541 _36539 P x f x' y h1)). Qed.
Lemma lem3462054 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term349 _89769 _89788 _89789 x f x' y.
Proof. exact (proj2 (@lem3461899 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462062 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term53 _89769 x t.
Proof. exact (proj2 (@lem3461904 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462066 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : t = (f x'' y').
Proof. exact (proj2 (@lem3461906 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462094 {_89769 _89788 _89789 : Type'} (_36542 : _89789) (_36543 : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term75 _89769 _89788 _89789 P x f _36542 _36543.
Proof. exact (EQ_MP (@lem3462037 _89769 _89788 _89789 P x f _36542 _36543) (@lem3462036 _89769 _89788 _89789 _36542 _36543 x'' y' t P x f h1)). Qed.
Lemma lem3462095 {_89769 : Type'} (x : _89769) : (term350 _89769 x) = (term350 _89769 x).
Proof. exact (eq_refl (term350 _89769 x)). Qed.
Lemma lem3462096 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : (term351 _89769 x t) = (term352 _89769 _89788 _89789 x f x'' y').
Proof. exact (MK_COMB (@lem3462095 _89769 x) (@lem3462066 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462097 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) : (term352 _89769 _89788 _89789 x f x'' y') = (term349 _89769 _89788 _89789 x f x'' y').
Proof. exact (eq_refl (term352 _89769 _89788 _89789 x f x'' y')). Qed.
Lemma lem3462098 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term353 _89769 x t) = (term353 _89769 x t).
Proof. exact (eq_refl (term353 _89769 x t)). Qed.
Lemma lem3462099 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (x : _89769) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) : ((term351 _89769 x t) = (term352 _89769 _89788 _89789 x f x'' y')) = ((term351 _89769 x t) = (term349 _89769 _89788 _89789 x f x'' y')).
Proof. exact (MK_COMB (@lem3462098 _89769 x t) (@lem3462097 _89769 _89788 _89789 x f x'' y')). Qed.
Lemma lem3462100 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term351 _89769 x t) = (term53 _89769 x t).
Proof. exact (eq_refl (term351 _89769 x t)). Qed.
Lemma lem3462101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3462102 {_89769 : Type'} (x : _89769) (t : _89769 -> Prop) : (term353 _89769 x t) = (term354 _89769 x t).
Proof. exact (MK_COMB (@lem3462101) (@lem3462100 _89769 x t)). Qed.
Lemma lem3462103 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) : (term349 _89769 _89788 _89789 x f x'' y') = (term349 _89769 _89788 _89789 x f x'' y').
Proof. exact (eq_refl (term349 _89769 _89788 _89789 x f x'' y')). Qed.
Lemma lem3462104 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (x : _89769) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) : ((term351 _89769 x t) = (term349 _89769 _89788 _89789 x f x'' y')) = ((term53 _89769 x t) = (term349 _89769 _89788 _89789 x f x'' y')).
Proof. exact (MK_COMB (@lem3462102 _89769 x t) (@lem3462103 _89769 _89788 _89789 x f x'' y')). Qed.
Lemma lem3462105 {_89769 _89788 _89789 : Type'} (t : _89769 -> Prop) (x : _89769) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) : ((term351 _89769 x t) = (term352 _89769 _89788 _89789 x f x'' y')) = ((term53 _89769 x t) = (term349 _89769 _89788 _89789 x f x'' y')).
Proof. exact (TRANS (@lem3462099 _89769 _89788 _89789 t x f x'' y') (@lem3462104 _89769 _89788 _89789 t x f x'' y')). Qed.
Lemma lem3462106 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : (term53 _89769 x t) = (term349 _89769 _89788 _89789 x f x'' y').
Proof. exact (EQ_MP (@lem3462105 _89769 _89788 _89789 t x f x'' y') (@lem3462096 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462107 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term349 _89769 _89788 _89789 x f x'' y'.
Proof. exact (EQ_MP (@lem3462106 _89769 _89788 _89789 x'' y' t P x f h1) (@lem3462062 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462184 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : P x' y.
Proof. exact (proj1 (@lem3461899 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462185 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term355 _89788 _89789 P x' y.
Proof. exact (fun h0 : term347 _89788 _89789 P x' y => @lem3462184 _89769 _89788 _89789 P x f x' y h1). Qed.
Lemma lem3462187 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3462188 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (x' : _89789) (y : _89788) : (term355 _89788 _89789 P x' y) = (P x' y).
Proof. exact (@lem3462187 (P x' y)). Qed.
Lemma lem3462189 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : P x' y.
Proof. exact (EQ_MP (@lem3462188 _89788 _89789 P x' y) (@lem3462185 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462191 {_89769 : Type'} (x : _89769 -> Prop) : x = x.
Proof. exact (@lem21386 (_89769 -> Prop) x). Qed.
Lemma lem3462192 {_89769 : Type'} (x : _89769 -> Prop) : x = x.
Proof. exact (@lem3462191 _89769 x). Qed.
Lemma lem3462193 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (f x' y) = (f x' y).
Proof. exact (@lem3462192 _89769 (f x' y)). Qed.
Lemma lem3462194 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : term357 _89769 _89788 _89789 f x' y.
Proof. exact (fun h0 : term358 _89769 _89788 _89789 f x' y => @lem3462193 _89769 _89788 _89789 f x' y). Qed.
Lemma lem3462196 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3462197 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term357 _89769 _89788 _89789 f x' y) = ((f x' y) = (f x' y)).
Proof. exact (@lem3462196 ((f x' y) = (f x' y))). Qed.
Lemma lem3462198 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (f x' y) = (f x' y).
Proof. exact (EQ_MP (@lem3462197 _89769 _89788 _89789 f x' y) (@lem3462194 _89769 _89788 _89789 f x' y)). Qed.
Lemma lem3462214 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3462215 {_89769 _89788 _89789 : Type'} (x : _89769) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term359 _89769 _89788 _89789 f _36540 _36541 x _36539) = (term360 _89769 _89788 _89789 x _36539 f _36540 _36541).
Proof. exact (@lem3462214 (@IN _89769 x _36539) (term348 _89769 _89788 _89789 _36539 f _36540 _36541)). Qed.
Lemma lem3462223 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term361 _89788 _89789 P _36540 _36541) = (term361 _89788 _89789 P _36540 _36541).
Proof. exact (eq_refl (term361 _89788 _89789 P _36540 _36541)). Qed.
Lemma lem3462224 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term346 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term362 _89769 _89788 _89789 P x _36539 f _36540 _36541).
Proof. exact (MK_COMB (@lem3462223 _89788 _89789 P _36540 _36541) (@lem3462215 _89769 _89788 _89789 x _36539 f _36540 _36541)). Qed.
Lemma lem3462228 (q : Prop) (p : Prop) (r : Prop) : (term363 p q r) = (term363 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3462229 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term362 _89769 _89788 _89789 P x _36539 f _36540 _36541) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541).
Proof. exact (@lem3462228 (@IN _89769 x _36539) (term347 _89788 _89789 P _36540 _36541) (term348 _89769 _89788 _89789 _36539 f _36540 _36541)). Qed.
Lemma lem3462247 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term346 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541).
Proof. exact (TRANS (@lem3462224 _89769 _89788 _89789 P x _36539 f _36540 _36541) (@lem3462229 _89769 _89788 _89789 x P _36539 f _36540 _36541)). Qed.
Lemma lem3462248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3462249 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term365 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term366 _89769 _89788 _89789 x P _36539 f _36540 _36541).
Proof. exact (MK_COMB (@lem3462248) (@lem3462247 _89769 _89788 _89789 x P _36539 f _36540 _36541)). Qed.
Lemma lem3462267 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541).
Proof. exact (eq_refl (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541)). Qed.
Lemma lem3462268 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : ((term346 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541)) = ((term364 _89769 _89788 _89789 x P _36539 f _36540 _36541) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541)).
Proof. exact (MK_COMB (@lem3462249 _89769 _89788 _89789 x P _36539 f _36540 _36541) (@lem3462267 _89769 _89788 _89789 x P _36539 f _36540 _36541)). Qed.
Lemma lem3462270 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3462271 (x : Prop) : (x = x) = True.
Proof. exact (@lem3462270 Prop x). Qed.
Lemma lem3462272 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : ((term364 _89769 _89788 _89789 x P _36539 f _36540 _36541) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541)) = True.
Proof. exact (@lem3462271 (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541)). Qed.
Lemma lem3462273 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : ((term346 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541)) = True.
Proof. exact (TRANS (@lem3462268 _89769 _89788 _89789 x P _36539 f _36540 _36541) (@lem3462272 _89769 _89788 _89789 x P _36539 f _36540 _36541)). Qed.
Lemma lem3462274 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : True = ((term346 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541)).
Proof. exact (SYM (@lem3462273 _89769 _89788 _89789 x P _36539 f _36540 _36541)). Qed.
Lemma lem3462275 {_89769 _89788 _89789 : Type'} (x : _89769) (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term346 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541).
Proof. exact (EQ_MP (@lem3462274 _89769 _89788 _89789 x P _36539 f _36540 _36541) (@lem0)). Qed.
Lemma lem3462276 {_89769 _89788 _89789 : Type'} (_36539 : _89769 -> Prop) (_36540 : _89789) (_36541 : _89788) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term364 _89769 _89788 _89789 x P _36539 f _36540 _36541.
Proof. exact (EQ_MP (@lem3462275 _89769 _89788 _89789 x P _36539 f _36540 _36541) (@lem3462050 _89769 _89788 _89789 _36540 _36541 _36539 P x f x' y h1)). Qed.
Lemma lem3462278 (b : Prop) (a : Prop) : (a \/ b) = (term367 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3462279 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) (x : _89769) (_36539 : _89769 -> Prop) : (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541) = (term368 _89769 _89788 _89789 P f _36540 _36541 x _36539).
Proof. exact (@lem3462278 (term36 _89769 _89788 _89789 P _36539 f _36540 _36541) (@IN _89769 x _36539)). Qed.
Lemma lem3462281 (a : Prop) (b : Prop) : (term369 a b) = (term370 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3462282 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term371 _89769 _89788 _89789 P _36539 f _36540 _36541) = (term372 _89769 _89788 _89789 P _36539 f _36540 _36541).
Proof. exact (@lem3462281 (term347 _89788 _89789 P _36540 _36541) (term348 _89769 _89788 _89789 _36539 f _36540 _36541)). Qed.
Lemma lem3462284 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3462285 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term373 _89788 _89789 P _36540 _36541) = (P _36540 _36541).
Proof. exact (@lem3462284 (P _36540 _36541)). Qed.
Lemma lem3462286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3462287 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term374 _89788 _89789 P _36540 _36541) = (term375 _89788 _89789 P _36540 _36541).
Proof. exact (MK_COMB (@lem3462286) (@lem3462285 _89788 _89789 P _36540 _36541)). Qed.
Lemma lem3462289 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3462290 {_89769 _89788 _89789 : Type'} (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term376 _89769 _89788 _89789 _36539 f _36540 _36541) = (_36539 = (f _36540 _36541)).
Proof. exact (@lem3462289 (_36539 = (f _36540 _36541))). Qed.
Lemma lem3462291 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term372 _89769 _89788 _89789 P _36539 f _36540 _36541) = (term22 _89769 _89788 _89789 P _36539 f _36540 _36541).
Proof. exact (MK_COMB (@lem3462287 _89788 _89789 P _36540 _36541) (@lem3462290 _89769 _89788 _89789 _36539 f _36540 _36541)). Qed.
Lemma lem3462292 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term371 _89769 _89788 _89789 P _36539 f _36540 _36541) = (term22 _89769 _89788 _89789 P _36539 f _36540 _36541).
Proof. exact (TRANS (@lem3462282 _89769 _89788 _89789 P _36539 f _36540 _36541) (@lem3462291 _89769 _89788 _89789 P _36539 f _36540 _36541)). Qed.
Lemma lem3462293 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3462294 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36539 : _89769 -> Prop) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) : (term377 _89769 _89788 _89789 P _36539 f _36540 _36541) = (term378 _89769 _89788 _89789 P _36539 f _36540 _36541).
Proof. exact (MK_COMB (@lem3462293) (@lem3462292 _89769 _89788 _89789 P _36539 f _36540 _36541)). Qed.
Lemma lem3462295 {_89769 : Type'} (x : _89769) (_36539 : _89769 -> Prop) : (@IN _89769 x _36539) = (@IN _89769 x _36539).
Proof. exact (eq_refl (@IN _89769 x _36539)). Qed.
Lemma lem3462296 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) (x : _89769) (_36539 : _89769 -> Prop) : (term368 _89769 _89788 _89789 P f _36540 _36541 x _36539) = (term379 _89769 _89788 _89789 P f _36540 _36541 x _36539).
Proof. exact (MK_COMB (@lem3462294 _89769 _89788 _89789 P _36539 f _36540 _36541) (@lem3462295 _89769 x _36539)). Qed.
Lemma lem3462297 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (_36540 : _89789) (_36541 : _89788) (x : _89769) (_36539 : _89769 -> Prop) : (term364 _89769 _89788 _89789 x P _36539 f _36540 _36541) = (term379 _89769 _89788 _89789 P f _36540 _36541 x _36539).
Proof. exact (TRANS (@lem3462279 _89769 _89788 _89789 P f _36540 _36541 x _36539) (@lem3462296 _89769 _89788 _89789 P f _36540 _36541 x _36539)). Qed.
Lemma lem3462299 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term380 _89769 _89788 _89789 P f x' y.
Proof. exact (conj (@lem3462189 _89769 _89788 _89789 P x f x' y h1) (@lem3462198 _89769 _89788 _89789 f x' y)). Qed.
Lemma lem3462301 {_89769 _89788 _89789 : Type'} (_36540 : _89789) (_36541 : _89788) (_36539 : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term379 _89769 _89788 _89789 P f _36540 _36541 x _36539.
Proof. exact (EQ_MP (@lem3462297 _89769 _89788 _89789 P f _36540 _36541 x _36539) (@lem3462276 _89769 _89788 _89789 _36539 _36540 _36541 P x f x' y h1)). Qed.
Lemma lem3462302 {_89769 _89788 _89789 : Type'} (_36540 : _89789) (_36541 : _89788) (_36539 : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term379 _89769 _89788 _89789 P f _36540 _36541 x _36539.
Proof. exact (@lem3462301 _89769 _89788 _89789 _36540 _36541 _36539 P x f x' y h1). Qed.
Lemma lem3462303 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term381 _89769 _89788 _89789 P x f x' y.
Proof. exact (@lem3462302 _89769 _89788 _89789 x' y (f x' y) P x f x' y h1). Qed.
Lemma lem3462306 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term74 _89769 _89788 _89789 x f x' y.
Proof. exact (@lem3462303 _89769 _89788 _89789 P x f x' y h1 (@lem3462299 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462307 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term382 _89769 _89788 _89789 x f x' y.
Proof. exact (fun h0 : term349 _89769 _89788 _89789 x f x' y => @lem3462306 _89769 _89788 _89789 P x f x' y h1). Qed.
Lemma lem3462309 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3462310 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term382 _89769 _89788 _89789 x f x' y) = (term74 _89769 _89788 _89789 x f x' y).
Proof. exact (@lem3462309 (term74 _89769 _89788 _89789 x f x' y)). Qed.
Lemma lem3462311 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term74 _89769 _89788 _89789 x f x' y.
Proof. exact (EQ_MP (@lem3462310 _89769 _89788 _89789 x f x' y) (@lem3462307 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462314 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3462316 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) : (term349 _89769 _89788 _89789 x f x' y) = (term383 _89769 _89788 _89789 x f x' y).
Proof. exact (@lem3462314 (term74 _89769 _89788 _89789 x f x' y)). Qed.
Lemma lem3462319 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term383 _89769 _89788 _89789 x f x' y.
Proof. exact (EQ_MP (@lem3462316 _89769 _89788 _89789 x f x' y) (@lem3462054 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462322 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : False.
Proof. exact (@lem3462319 _89769 _89788 _89789 P x f x' y h1 (@lem3462311 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462323 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : term384.
Proof. exact (fun h0 : ~ False => @lem3462322 _89769 _89788 _89789 P x f x' y h1). Qed.
Lemma lem3462325 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3462326 : term384 = False.
Proof. exact (@lem3462325 False). Qed.
Lemma lem3462327 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (x' : _89789) (y : _89788) (h1 : term130 _89769 _89788 _89789 P x f x' y) : False.
Proof. exact (EQ_MP (@lem3462326) (@lem3462323 _89769 _89788 _89789 P x f x' y h1)). Qed.
Lemma lem3462329 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : P x'' y'.
Proof. exact (proj1 (@lem3461906 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462330 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term355 _89788 _89789 P x'' y'.
Proof. exact (fun h0 : term347 _89788 _89789 P x'' y' => @lem3462329 _89769 _89788 _89789 x'' y' t P x f h1). Qed.
Lemma lem3462332 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3462333 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (x'' : _89789) (y' : _89788) : (term355 _89788 _89789 P x'' y') = (P x'' y').
Proof. exact (@lem3462332 (P x'' y')). Qed.
Lemma lem3462334 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : P x'' y'.
Proof. exact (EQ_MP (@lem3462333 _89788 _89789 P x'' y') (@lem3462330 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462340 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3462341 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term75 _89769 _89788 _89789 P x f _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543).
Proof. exact (@lem3462340 (term74 _89769 _89788 _89789 x f _36542 _36543) (term347 _89788 _89789 P _36542 _36543)). Qed.
Lemma lem3462347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3462348 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term386 _89769 _89788 _89789 P x f _36542 _36543) = (term387 _89769 _89788 _89789 x f P _36542 _36543).
Proof. exact (MK_COMB (@lem3462347) (@lem3462341 _89769 _89788 _89789 x f P _36542 _36543)). Qed.
Lemma lem3462354 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term385 _89769 _89788 _89789 x f P _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543).
Proof. exact (eq_refl (term385 _89769 _89788 _89789 x f P _36542 _36543)). Qed.
Lemma lem3462355 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : ((term75 _89769 _89788 _89789 P x f _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543)) = ((term385 _89769 _89788 _89789 x f P _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543)).
Proof. exact (MK_COMB (@lem3462348 _89769 _89788 _89789 x f P _36542 _36543) (@lem3462354 _89769 _89788 _89789 x f P _36542 _36543)). Qed.
Lemma lem3462357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3462358 (x : Prop) : (x = x) = True.
Proof. exact (@lem3462357 Prop x). Qed.
Lemma lem3462359 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : ((term385 _89769 _89788 _89789 x f P _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543)) = True.
Proof. exact (@lem3462358 (term385 _89769 _89788 _89789 x f P _36542 _36543)). Qed.
Lemma lem3462360 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : ((term75 _89769 _89788 _89789 P x f _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543)) = True.
Proof. exact (TRANS (@lem3462355 _89769 _89788 _89789 x f P _36542 _36543) (@lem3462359 _89769 _89788 _89789 x f P _36542 _36543)). Qed.
Lemma lem3462361 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : True = ((term75 _89769 _89788 _89789 P x f _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543)).
Proof. exact (SYM (@lem3462360 _89769 _89788 _89789 x f P _36542 _36543)). Qed.
Lemma lem3462362 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term75 _89769 _89788 _89789 P x f _36542 _36543) = (term385 _89769 _89788 _89789 x f P _36542 _36543).
Proof. exact (EQ_MP (@lem3462361 _89769 _89788 _89789 x f P _36542 _36543) (@lem0)). Qed.
Lemma lem3462363 {_89769 _89788 _89789 : Type'} (_36542 : _89789) (_36543 : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term385 _89769 _89788 _89789 x f P _36542 _36543.
Proof. exact (EQ_MP (@lem3462362 _89769 _89788 _89789 x f P _36542 _36543) (@lem3462094 _89769 _89788 _89789 _36542 _36543 x'' y' t P x f h1)). Qed.
Lemma lem3462365 (b : Prop) (a : Prop) : (a \/ b) = (term367 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3462366 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term385 _89769 _89788 _89789 x f P _36542 _36543) = (term388 _89769 _89788 _89789 P x f _36542 _36543).
Proof. exact (@lem3462365 (term347 _89788 _89789 P _36542 _36543) (term74 _89769 _89788 _89789 x f _36542 _36543)). Qed.
Lemma lem3462368 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3462369 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term373 _89788 _89789 P _36542 _36543) = (P _36542 _36543).
Proof. exact (@lem3462368 (P _36542 _36543)). Qed.
Lemma lem3462370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3462371 {_89788 _89789 : Type'} (P : type1470 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term389 _89788 _89789 P _36542 _36543) = (term390 _89788 _89789 P _36542 _36543).
Proof. exact (MK_COMB (@lem3462370) (@lem3462369 _89788 _89789 P _36542 _36543)). Qed.
Lemma lem3462372 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term74 _89769 _89788 _89789 x f _36542 _36543) = (term74 _89769 _89788 _89789 x f _36542 _36543).
Proof. exact (eq_refl (term74 _89769 _89788 _89789 x f _36542 _36543)). Qed.
Lemma lem3462373 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term388 _89769 _89788 _89789 P x f _36542 _36543) = (term17 _89769 _89788 _89789 P x f _36542 _36543).
Proof. exact (MK_COMB (@lem3462371 _89788 _89789 P _36542 _36543) (@lem3462372 _89769 _89788 _89789 x f _36542 _36543)). Qed.
Lemma lem3462374 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (_36542 : _89789) (_36543 : _89788) : (term385 _89769 _89788 _89789 x f P _36542 _36543) = (term17 _89769 _89788 _89789 P x f _36542 _36543).
Proof. exact (TRANS (@lem3462366 _89769 _89788 _89789 P x f _36542 _36543) (@lem3462373 _89769 _89788 _89789 P x f _36542 _36543)). Qed.
Lemma lem3462377 {_89769 _89788 _89789 : Type'} (_36542 : _89789) (_36543 : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term17 _89769 _89788 _89789 P x f _36542 _36543.
Proof. exact (EQ_MP (@lem3462374 _89769 _89788 _89789 P x f _36542 _36543) (@lem3462363 _89769 _89788 _89789 _36542 _36543 x'' y' t P x f h1)). Qed.
Lemma lem3462378 {_89769 _89788 _89789 : Type'} (_36542 : _89789) (_36543 : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term17 _89769 _89788 _89789 P x f _36542 _36543.
Proof. exact (@lem3462377 _89769 _89788 _89789 _36542 _36543 x'' y' t P x f h1). Qed.
Lemma lem3462379 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term17 _89769 _89788 _89789 P x f x'' y'.
Proof. exact (@lem3462378 _89769 _89788 _89789 x'' y' x'' y' t P x f h1). Qed.
Lemma lem3462382 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term74 _89769 _89788 _89789 x f x'' y'.
Proof. exact (@lem3462379 _89769 _89788 _89789 x'' y' t P x f h1 (@lem3462334 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462383 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term382 _89769 _89788 _89789 x f x'' y'.
Proof. exact (fun h0 : term349 _89769 _89788 _89789 x f x'' y' => @lem3462382 _89769 _89788 _89789 x'' y' t P x f h1). Qed.
Lemma lem3462385 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3462386 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) : (term382 _89769 _89788 _89789 x f x'' y') = (term74 _89769 _89788 _89789 x f x'' y').
Proof. exact (@lem3462385 (term74 _89769 _89788 _89789 x f x'' y')). Qed.
Lemma lem3462387 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term74 _89769 _89788 _89789 x f x'' y'.
Proof. exact (EQ_MP (@lem3462386 _89769 _89788 _89789 x f x'' y') (@lem3462383 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462390 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3462392 {_89769 _89788 _89789 : Type'} (x : _89769) (f : type1517 _89769 _89788 _89789) (x'' : _89789) (y' : _89788) : (term349 _89769 _89788 _89789 x f x'' y') = (term383 _89769 _89788 _89789 x f x'' y').
Proof. exact (@lem3462390 (term74 _89769 _89788 _89789 x f x'' y')). Qed.
Lemma lem3462395 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term383 _89769 _89788 _89789 x f x'' y'.
Proof. exact (EQ_MP (@lem3462392 _89769 _89788 _89789 x f x'' y') (@lem3462107 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462398 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : False.
Proof. exact (@lem3462395 _89769 _89788 _89789 x'' y' t P x f h1 (@lem3462387 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462399 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : term384.
Proof. exact (fun h0 : ~ False => @lem3462398 _89769 _89788 _89789 x'' y' t P x f h1). Qed.
Lemma lem3462401 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3462402 : term384 = False.
Proof. exact (@lem3462401 False). Qed.
Lemma lem3462404 {_89769 _89788 _89789 : Type'} (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term216 _89769 _89788 _89789 x'' y' t P x f) : False.
Proof. exact (EQ_MP (@lem3462402) (@lem3462399 _89769 _89788 _89789 x'' y' t P x f h1)). Qed.
Lemma lem3462405 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term293 _89769 _89788 _89789 x' y x'' y' t P x f) : False.
Proof. exact (or_elim (@lem3461896 _89769 _89788 _89789 x' y x'' y' t P x f h1) (fun h0 : term130 _89769 _89788 _89789 P x f x' y => @lem3462327 _89769 _89788 _89789 P x f x' y h0) (fun h0 : term216 _89769 _89788 _89789 x'' y' t P x f => @lem3462404 _89769 _89788 _89789 x'' y' t P x f h0)). Qed.
Lemma lem3462406 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term293 _89769 _89788 _89789 x' y x'' y' t P x f) : (term293 _89769 _89788 _89789 x' y x'' y' t P x f) = False.
Proof. exact (prop_ext (fun h2 : term293 _89769 _89788 _89789 x' y x'' y' t P x f => @lem3462405 _89769 _89788 _89789 x' y x'' y' t P x f h1) (fun h2 : False => @lem3461896 _89769 _89788 _89789 x' y x'' y' t P x f h1)). Qed.
Lemma lem3462407 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (y' : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term293 _89769 _89788 _89789 x' y x'' y' t P x f) : False.
Proof. exact (EQ_MP (@lem3462406 _89769 _89788 _89789 x' y x'' y' t P x f h1) (@lem3461896 _89769 _89788 _89789 x' y x'' y' t P x f h1)). Qed.
Lemma lem3462408 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (x'' : _89789) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term296 _89769 _89788 _89789 x' y x'' t P x f) : False.
Proof. exact (ex_elim (@lem3461776 _89769 _89788 _89789 x' y x'' t P x f h1) (fun y' : _89788 => fun h0 : term295 _89769 _89788 _89789 x' y x'' t P x f y' => @lem3462407 _89769 _89788 _89789 x' y x'' y' t P x f h0)). Qed.
Lemma lem3462409 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (t : _89769 -> Prop) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term298 _89769 _89788 _89789 x' y t P x f) : False.
Proof. exact (ex_elim (@lem3461775 _89769 _89788 _89789 x' y t P x f h1) (fun x'' : _89789 => fun h0 : term297 _89769 _89788 _89789 x' y t P x f x'' => @lem3462408 _89769 _89788 _89789 x' y x'' t P x f h0)). Qed.
Lemma lem3462410 {_89769 _89788 _89789 : Type'} (x' : _89789) (y : _89788) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term300 _89769 _89788 _89789 x' y P x f) : False.
Proof. exact (ex_elim (@lem3461774 _89769 _89788 _89789 x' y P x f h1) (fun t : _89769 -> Prop => fun h0 : term299 _89769 _89788 _89789 x' y P x f t => @lem3462409 _89769 _89788 _89789 x' y t P x f h0)). Qed.
Lemma lem3462411 {_89769 _89788 _89789 : Type'} (x' : _89789) (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term302 _89769 _89788 _89789 x' P x f) : False.
Proof. exact (ex_elim (@lem3461773 _89769 _89788 _89789 x' P x f h1) (fun y : _89788 => fun h0 : term301 _89769 _89788 _89789 x' P x f y => @lem3462410 _89769 _89788 _89789 x' y P x f h0)). Qed.
Lemma lem3462412 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term34 _89769 _89788 _89789 P x f) : False.
Proof. exact (ex_elim (@lem3461772 _89769 _89788 _89789 P x f h1) (fun x' : _89789 => fun h0 : term303 _89769 _89788 _89789 P x f x' => @lem3462411 _89769 _89788 _89789 x' P x f h0)). Qed.
Lemma lem3462413 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term34 _89769 _89788 _89789 P x f) : (term34 _89769 _89788 _89789 P x f) = False.
Proof. exact (prop_ext (fun h2 : term34 _89769 _89788 _89789 P x f => @lem3462412 _89769 _89788 _89789 P x f h1) (fun h2 : False => @lem3461034 _89769 _89788 _89789 P x f h1)). Qed.
Lemma lem3462414 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) (h1 : term34 _89769 _89788 _89789 P x f) : False.
Proof. exact (EQ_MP (@lem3462413 _89769 _89788 _89789 P x f h1) (@lem3461034 _89769 _89788 _89789 P x f h1)). Qed.
Lemma lem3462415 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : term33 _89769 _89788 _89789 P x f.
Proof. exact (fun h0 : term34 _89769 _89788 _89789 P x f => @lem3462414 _89769 _89788 _89789 P x f h0). Qed.
Lemma lem3462416 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (x : _89769) (f : type1517 _89769 _89788 _89789) : (term30 _89769 _89788 _89789 P f x) = (term21 _89769 _89788 _89789 P x f).
Proof. exact (EQ_MP (@lem3461033 _89769 _89788 _89789 P x f) (@lem3462415 _89769 _89788 _89789 P x f)). Qed.
Lemma lem3462421 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term1 _89769 _89788 _89789 P f.
Proof. exact (fun x : _89769 => @lem3462416 _89769 _89788 _89789 P x f). Qed.
Lemma lem3462426 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : term12 _89769 _89788 _89789 f.
Proof. exact (fun P : type1470 _89788 _89789 => @lem3462421 _89769 _89788 _89789 P f). Qed.
Lemma lem3462431 {_89769 _89788 _89789 : Type'} : term16 _89769 _89788 _89789.
Proof. exact (fun f : type1517 _89769 _89788 _89789 => @lem3462426 _89769 _89788 _89789 f). Qed.
Lemma lem3462432 {_89769 _89788 _89789 : Type'} : term15 _89769 _89788 _89789.
Proof. exact (EQ_MP (@lem3461029 _89769 _89788 _89789) (@lem3462431 _89769 _89788 _89789)). Qed.
Lemma lem3462433 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : term391 _89769 _89788 _89789 f.
Proof. exact (@lem3462432 _89769 _89788 _89789 f). Qed.
Lemma lem3462434 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : (term391 _89769 _89788 _89789 f) = (term11 _89769 _89788 _89789 f).
Proof. exact (eq_refl (term391 _89769 _89788 _89789 f)). Qed.
Lemma lem3462435 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) : term11 _89769 _89788 _89789 f.
Proof. exact (EQ_MP (@lem3462434 _89769 _89788 _89789 f) (@lem3462433 _89769 _89788 _89789 f)). Qed.
Lemma lem3462436 {_89769 _89788 _89789 : Type'} (f : type1517 _89769 _89788 _89789) (P : type1470 _89788 _89789) : term392 _89769 _89788 _89789 f P.
Proof. exact (@lem3462435 _89769 _89788 _89789 f P). Qed.
Lemma lem3462437 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term392 _89769 _89788 _89789 f P) = (term2 _89769 _89788 _89789 P f).
Proof. exact (eq_refl (term392 _89769 _89788 _89789 f P)). Qed.
Lemma lem3462438 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term2 _89769 _89788 _89789 P f.
Proof. exact (EQ_MP (@lem3462437 _89769 _89788 _89789 P f) (@lem3462436 _89769 _89788 _89789 f P)). Qed.
Lemma lem3462440 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term2 _89769 _89788 _89789 P f.
Proof. exact (@lem3460823 _89769 _89788 _89789 P f (@lem3462438 _89769 _89788 _89789 P f)). Qed.
Lemma lem3462441 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term3 _89769 _89788 _89789 P f) : False.
Proof. exact (@lem3462440 _89769 _89788 _89789 P f (@lem3460807 _89769 _89788 _89789 P f h1)). Qed.
Lemma lem3462442 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term3 _89769 _89788 _89789 P f) : (term3 _89769 _89788 _89789 P f) = False.
Proof. exact (prop_ext (fun h2 : term3 _89769 _89788 _89789 P f => @lem3462441 _89769 _89788 _89789 P f h1) (fun h2 : False => @lem3460807 _89769 _89788 _89789 P f h1)). Qed.
Lemma lem3462443 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) (h1 : term3 _89769 _89788 _89789 P f) : False.
Proof. exact (EQ_MP (@lem3462442 _89769 _89788 _89789 P f h1) (@lem3460807 _89769 _89788 _89789 P f h1)). Qed.
Lemma lem3462444 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term2 _89769 _89788 _89789 P f.
Proof. exact (fun h0 : term3 _89769 _89788 _89789 P f => @lem3462443 _89769 _89788 _89789 P f h0). Qed.
Lemma lem3462445 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term1 _89769 _89788 _89789 P f.
Proof. exact (EQ_MP (@lem3460806 _89769 _89788 _89789 P f) (@lem3462444 _89769 _89788 _89789 P f)). Qed.
