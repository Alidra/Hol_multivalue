Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_ALT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3560920 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3560921 {_91244 _91249 : Type'} : (term1 _91244 _91249) = (term2 _91244 _91249).
Proof. exact (@lem3560920 (term1 _91244 _91249)). Qed.
Lemma lem3560922 {_91244 _91249 : Type'} : (term2 _91244 _91249) = (term1 _91244 _91249).
Proof. exact (SYM (@lem3560921 _91244 _91249)). Qed.
Lemma lem3560923 {_91244 _91249 : Type'} (h1 : term3 _91244 _91249) : term3 _91244 _91249.
Proof. exact (h1). Qed.
Lemma lem3560926 {_91244 _91249 : Type'} (h1 : term2 _91244 _91249) : term2 _91244 _91249.
Proof. exact (h1). Qed.
Lemma lem3560927 {_91244 _91249 : Type'} : term4 _91244 _91249.
Proof. exact (fun h0 : term2 _91244 _91249 => @lem3560926 _91244 _91249 h0). Qed.
Lemma lem3560928 {_91244 _91249 : Type'} (h1 : term4 _91244 _91249) : term4 _91244 _91249.
Proof. exact (h1). Qed.
Lemma lem3560929 {_91244 _91249 : Type'} (h1 : term2 _91244 _91249) : term2 _91244 _91249.
Proof. exact (h1). Qed.
Lemma lem3560930 {_91244 _91249 : Type'} (h1 : term2 _91244 _91249) (h2 : term4 _91244 _91249) : term2 _91244 _91249.
Proof. exact (@lem3560928 _91244 _91249 h2 (@lem3560929 _91244 _91249 h1)). Qed.
Lemma lem3560931 {_91244 _91249 : Type'} (h1 : term2 _91244 _91249) : term5 _91244 _91249.
Proof. exact (fun h0 : term4 _91244 _91249 => @lem3560930 _91244 _91249 h1 h0). Qed.
Lemma lem3560932 {_91244 _91249 : Type'} (h1 : term4 _91244 _91249) : term4 _91244 _91249.
Proof. exact (h1). Qed.
Lemma lem3560933 {_91244 _91249 : Type'} (h1 : term2 _91244 _91249) (h2 : term4 _91244 _91249) : term2 _91244 _91249.
Proof. exact (@lem3560931 _91244 _91249 h1 (@lem3560932 _91244 _91249 h2)). Qed.
Lemma lem3560934 {_91244 _91249 : Type'} (h1 : term4 _91244 _91249) : term4 _91244 _91249.
Proof. exact (fun h0 : term2 _91244 _91249 => @lem3560933 _91244 _91249 h0 h1). Qed.
Lemma lem3560935 {_91244 _91249 : Type'} : term6 _91244 _91249.
Proof. exact (fun h0 : term4 _91244 _91249 => @lem3560934 _91244 _91249 h0). Qed.
Lemma lem3560938 {_91244 _91249 : Type'} : term4 _91244 _91249.
Proof. exact (@lem3560935 _91244 _91249 (@lem3560927 _91244 _91249)). Qed.
Lemma lem3560939 {_91244 _91249 : Type'} : term4 _91244 _91249.
Proof. exact (@lem3560938 _91244 _91249). Qed.
Lemma lem3560941 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3560942 {_91244 _91249 : Type'} : (term2 _91244 _91249) = (term7 _91244 _91249).
Proof. exact (@lem3560941 (term3 _91244 _91249)). Qed.
Lemma lem3560944 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3560945 {_91244 _91249 : Type'} : (term7 _91244 _91249) = (term1 _91244 _91249).
Proof. exact (@lem3560944 (term1 _91244 _91249)). Qed.
Lemma lem3560972 {_91244 _91249 : Type'} : (term2 _91244 _91249) = (term1 _91244 _91249).
Proof. exact (TRANS (@lem3560942 _91244 _91249) (@lem3560945 _91244 _91249)). Qed.
Lemma lem3560977 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (((f x) = (f y)) = (x = y)) = (((f x) = (f y)) = (x = y)).
Proof. exact (eq_refl (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3560978 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term9 _91244 _91249 f x) = (term9 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3560977 _91244 _91249 f x y)). Qed.
Lemma lem3560979 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3560980 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term10 _91244 _91249 f x) = (term10 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3560979 _91249) (@lem3560978 _91244 _91249 f x)). Qed.
Lemma lem3560981 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term11 _91244 _91249 f) = (term11 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3560980 _91244 _91249 f x)). Qed.
Lemma lem3560982 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3560983 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term12 _91244 _91249 f) = (term12 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3560982 _91249) (@lem3560981 _91244 _91249 f)). Qed.
Lemma lem3560988 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term13 _91244 _91249 f x y) = (term13 _91244 _91249 f x y).
Proof. exact (eq_refl (term13 _91244 _91249 f x y)). Qed.
Lemma lem3560989 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term14 _91244 _91249 f x) = (term14 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3560988 _91244 _91249 f x y)). Qed.
Lemma lem3560990 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3560991 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term15 _91244 _91249 f x) = (term15 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3560990 _91249) (@lem3560989 _91244 _91249 f x)). Qed.
Lemma lem3560992 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term16 _91244 _91249 f) = (term16 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3560991 _91244 _91249 f x)). Qed.
Lemma lem3560993 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3560994 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term17 _91244 _91249 f) = (term17 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3560993 _91249) (@lem3560992 _91244 _91249 f)). Qed.
Lemma lem3560995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3560996 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term18 _91244 _91249 f) = (term18 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3560995) (@lem3560994 _91244 _91249 f)). Qed.
Lemma lem3560997 {_91244 _91249 : Type'} (f : _91249 -> _91244) : ((term17 _91244 _91249 f) = (term12 _91244 _91249 f)) = ((term17 _91244 _91249 f) = (term12 _91244 _91249 f)).
Proof. exact (MK_COMB (@lem3560996 _91244 _91249 f) (@lem3560983 _91244 _91249 f)). Qed.
Lemma lem3560998 {_91244 _91249 : Type'} : (term19 _91244 _91249) = (term19 _91244 _91249).
Proof. exact (fun_ext (fun f : _91249 -> _91244 => @lem3560997 _91244 _91249 f)). Qed.
Lemma lem3560999 {_91244 _91249 : Type'} : (@all (_91249 -> _91244)) = (@all (_91249 -> _91244)).
Proof. exact (eq_refl (@all (_91249 -> _91244))). Qed.
Lemma lem3561000 {_91244 _91249 : Type'} : (term1 _91244 _91249) = (term1 _91244 _91249).
Proof. exact (MK_COMB (@lem3560999 _91244 _91249) (@lem3560998 _91244 _91249)). Qed.
Lemma lem3561035 {_91244 _91249 : Type'} : (term2 _91244 _91249) = (term1 _91244 _91249).
Proof. exact (TRANS (@lem3560972 _91244 _91249) (@lem3561000 _91244 _91249)). Qed.
Lemma lem3561036 {_91244 _91249 : Type'} : (term1 _91244 _91249) = (term2 _91244 _91249).
Proof. exact (SYM (@lem3561035 _91244 _91249)). Qed.
Lemma lem3561038 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3561039 {_91244 _91249 : Type'} (f : _91249 -> _91244) : ((term17 _91244 _91249 f) = (term12 _91244 _91249 f)) = (term20 _91244 _91249 f).
Proof. exact (@lem3561038 ((term17 _91244 _91249 f) = (term12 _91244 _91249 f))). Qed.
Lemma lem3561040 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term20 _91244 _91249 f) = ((term17 _91244 _91249 f) = (term12 _91244 _91249 f)).
Proof. exact (SYM (@lem3561039 _91244 _91249 f)). Qed.
Lemma lem3561041 {_91244 _91249 : Type'} (f : _91249 -> _91244) (h1 : term21 _91244 _91249 f) : term21 _91244 _91249 f.
Proof. exact (h1). Qed.
Lemma lem3561050 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term22 _91244 _91249 f x y) = (term23 _91244 _91249 f x y).
Proof. exact (@lem17362 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3561055 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term13 _91244 _91249 f x y) = (term24 _91244 _91249 f x y).
Proof. exact (@lem17265 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3561056 {_91249 : Type'} (P : _91249 -> Prop) : (term25 _91249 P) = (term26 _91249 P).
Proof. exact (@lem18392 _91249 P). Qed.
Lemma lem3561057 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term27 _91244 _91249 f x) = (term28 _91244 _91249 f x).
Proof. exact (@lem3561056 _91249 (term14 _91244 _91249 f x)). Qed.
Lemma lem3561058 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term29 _91244 _91249 f x y) = (term13 _91244 _91249 f x y).
Proof. exact (eq_refl (term29 _91244 _91249 f x y)). Qed.
Lemma lem3561059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3561060 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term30 _91244 _91249 f x y) = (term22 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561059) (@lem3561058 _91244 _91249 f x y)). Qed.
Lemma lem3561061 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term30 _91244 _91249 f x y) = (term23 _91244 _91249 f x y).
Proof. exact (TRANS (@lem3561060 _91244 _91249 f x y) (@lem3561050 _91244 _91249 f x y)). Qed.
Lemma lem3561062 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term31 _91244 _91249 f x) = (term32 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561061 _91244 _91249 f x y)). Qed.
Lemma lem3561063 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561064 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term28 _91244 _91249 f x) = (term33 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561063 _91249) (@lem3561062 _91244 _91249 f x)). Qed.
Lemma lem3561065 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term27 _91244 _91249 f x) = (term33 _91244 _91249 f x).
Proof. exact (TRANS (@lem3561057 _91244 _91249 f x) (@lem3561064 _91244 _91249 f x)). Qed.
Lemma lem3561066 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term14 _91244 _91249 f x) = (term34 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561055 _91244 _91249 f x y)). Qed.
Lemma lem3561067 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561068 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term15 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561067 _91249) (@lem3561066 _91244 _91249 f x)). Qed.
Lemma lem3561069 {_91249 : Type'} (P : _91249 -> Prop) : (term25 _91249 P) = (term26 _91249 P).
Proof. exact (@lem18392 _91249 P). Qed.
Lemma lem3561070 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term36 _91244 _91249 f) = (term37 _91244 _91249 f).
Proof. exact (@lem3561069 _91249 (term16 _91244 _91249 f)). Qed.
Lemma lem3561071 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term38 _91244 _91249 f x) = (term15 _91244 _91249 f x).
Proof. exact (eq_refl (term38 _91244 _91249 f x)). Qed.
Lemma lem3561072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3561073 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term39 _91244 _91249 f x) = (term27 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561072) (@lem3561071 _91244 _91249 f x)). Qed.
Lemma lem3561074 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term39 _91244 _91249 f x) = (term33 _91244 _91249 f x).
Proof. exact (TRANS (@lem3561073 _91244 _91249 f x) (@lem3561065 _91244 _91249 f x)). Qed.
Lemma lem3561075 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term40 _91244 _91249 f) = (term41 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561074 _91244 _91249 f x)). Qed.
Lemma lem3561076 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561077 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term37 _91244 _91249 f) = (term42 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561076 _91249) (@lem3561075 _91244 _91249 f)). Qed.
Lemma lem3561078 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term36 _91244 _91249 f) = (term42 _91244 _91249 f).
Proof. exact (TRANS (@lem3561070 _91244 _91249 f) (@lem3561077 _91244 _91249 f)). Qed.
Lemma lem3561079 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term16 _91244 _91249 f) = (term43 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561068 _91244 _91249 f x)). Qed.
Lemma lem3561080 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561081 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term17 _91244 _91249 f) = (term44 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561080 _91249) (@lem3561079 _91244 _91249 f)). Qed.
Lemma lem3561096 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term45 _91244 _91249 f x y) = (term46 _91244 _91249 f x y).
Proof. exact (@lem17930 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3561107 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (((f x) = (f y)) = (x = y)) = (term47 _91244 _91249 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3561108 {_91249 : Type'} (P : _91249 -> Prop) : (term25 _91249 P) = (term26 _91249 P).
Proof. exact (@lem18392 _91249 P). Qed.
Lemma lem3561109 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term48 _91244 _91249 f x) = (term49 _91244 _91249 f x).
Proof. exact (@lem3561108 _91249 (term9 _91244 _91249 f x)). Qed.
Lemma lem3561110 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term50 _91244 _91249 f x y) = (((f x) = (f y)) = (x = y)).
Proof. exact (eq_refl (term50 _91244 _91249 f x y)). Qed.
Lemma lem3561111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3561112 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term51 _91244 _91249 f x y) = (term45 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561111) (@lem3561110 _91244 _91249 f x y)). Qed.
Lemma lem3561113 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term51 _91244 _91249 f x y) = (term46 _91244 _91249 f x y).
Proof. exact (TRANS (@lem3561112 _91244 _91249 f x y) (@lem3561096 _91244 _91249 f x y)). Qed.
Lemma lem3561114 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term52 _91244 _91249 f x) = (term53 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561113 _91244 _91249 f x y)). Qed.
Lemma lem3561115 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561116 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term49 _91244 _91249 f x) = (term54 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561115 _91249) (@lem3561114 _91244 _91249 f x)). Qed.
Lemma lem3561117 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term48 _91244 _91249 f x) = (term54 _91244 _91249 f x).
Proof. exact (TRANS (@lem3561109 _91244 _91249 f x) (@lem3561116 _91244 _91249 f x)). Qed.
Lemma lem3561118 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term9 _91244 _91249 f x) = (term55 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561107 _91244 _91249 f x y)). Qed.
Lemma lem3561119 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561120 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term10 _91244 _91249 f x) = (term56 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561119 _91249) (@lem3561118 _91244 _91249 f x)). Qed.
Lemma lem3561121 {_91249 : Type'} (P : _91249 -> Prop) : (term25 _91249 P) = (term26 _91249 P).
Proof. exact (@lem18392 _91249 P). Qed.
Lemma lem3561122 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term57 _91244 _91249 f) = (term58 _91244 _91249 f).
Proof. exact (@lem3561121 _91249 (term11 _91244 _91249 f)). Qed.
Lemma lem3561123 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term59 _91244 _91249 f x) = (term10 _91244 _91249 f x).
Proof. exact (eq_refl (term59 _91244 _91249 f x)). Qed.
Lemma lem3561124 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3561125 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term60 _91244 _91249 f x) = (term48 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561124) (@lem3561123 _91244 _91249 f x)). Qed.
Lemma lem3561126 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term60 _91244 _91249 f x) = (term54 _91244 _91249 f x).
Proof. exact (TRANS (@lem3561125 _91244 _91249 f x) (@lem3561117 _91244 _91249 f x)). Qed.
Lemma lem3561127 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term61 _91244 _91249 f) = (term62 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561126 _91244 _91249 f x)). Qed.
Lemma lem3561128 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561129 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term58 _91244 _91249 f) = (term63 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561128 _91249) (@lem3561127 _91244 _91249 f)). Qed.
Lemma lem3561130 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term57 _91244 _91249 f) = (term63 _91244 _91249 f).
Proof. exact (TRANS (@lem3561122 _91244 _91249 f) (@lem3561129 _91244 _91249 f)). Qed.
Lemma lem3561131 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term11 _91244 _91249 f) = (term64 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561120 _91244 _91249 f x)). Qed.
Lemma lem3561132 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561133 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term12 _91244 _91249 f) = (term65 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561132 _91249) (@lem3561131 _91244 _91249 f)). Qed.
Lemma lem3561134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561135 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term66 _91244 _91249 f) = (term67 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561134) (@lem3561078 _91244 _91249 f)). Qed.
Lemma lem3561136 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term68 _91244 _91249 f) = (term69 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561135 _91244 _91249 f) (@lem3561133 _91244 _91249 f)). Qed.
Lemma lem3561137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561138 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term70 _91244 _91249 f) = (term71 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561137) (@lem3561081 _91244 _91249 f)). Qed.
Lemma lem3561139 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term72 _91244 _91249 f) = (term73 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561138 _91244 _91249 f) (@lem3561130 _91244 _91249 f)). Qed.
Lemma lem3561140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3561141 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term74 _91244 _91249 f) = (term75 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561140) (@lem3561139 _91244 _91249 f)). Qed.
Lemma lem3561142 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term76 _91244 _91249 f) = (term77 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561141 _91244 _91249 f) (@lem3561136 _91244 _91249 f)). Qed.
Lemma lem3561143 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term21 _91244 _91249 f) = (term76 _91244 _91249 f).
Proof. exact (@lem17646 (term17 _91244 _91249 f) (term12 _91244 _91249 f)). Qed.
Lemma lem3561144 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term21 _91244 _91249 f) = (term77 _91244 _91249 f).
Proof. exact (TRANS (@lem3561143 _91244 _91249 f) (@lem3561142 _91244 _91249 f)). Qed.
Lemma lem3561306 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3561307 {_91249 : Type'} (P : _91249 -> Prop) (Q : _91249 -> Prop) : (term78 _91249 P Q) = (term79 _91249 P Q).
Proof. exact (@lem3561306 _91249 P Q). Qed.
Lemma lem3561308 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term80 _91244 _91249 f x) = (term81 _91244 _91249 f x).
Proof. exact (@lem3561307 _91249 (term82 _91244 _91249 f x) (term34 _91244 _91249 f x)). Qed.
Lemma lem3561309 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term83 _91244 _91249 f x y) = (term84 _91244 _91249 f x y).
Proof. exact (eq_refl (term83 _91244 _91249 f x y)). Qed.
Lemma lem3561310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561311 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term85 _91244 _91249 f x y) = (term86 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561310) (@lem3561309 _91244 _91249 f x y)). Qed.
Lemma lem3561312 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term87 _91244 _91249 f x y) = (term24 _91244 _91249 f x y).
Proof. exact (eq_refl (term87 _91244 _91249 f x y)). Qed.
Lemma lem3561313 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term88 _91244 _91249 f x y) = (term47 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561311 _91244 _91249 f x y) (@lem3561312 _91244 _91249 f x y)). Qed.
Lemma lem3561314 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term89 _91244 _91249 f x) = (term55 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561313 _91244 _91249 f x y)). Qed.
Lemma lem3561315 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561316 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term80 _91244 _91249 f x) = (term56 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561315 _91249) (@lem3561314 _91244 _91249 f x)). Qed.
Lemma lem3561317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561318 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term90 _91244 _91249 f x) = (term91 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561317) (@lem3561316 _91244 _91249 f x)). Qed.
Lemma lem3561319 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term83 _91244 _91249 f x y) = (term84 _91244 _91249 f x y).
Proof. exact (eq_refl (term83 _91244 _91249 f x y)). Qed.
Lemma lem3561320 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term92 _91244 _91249 f x) = (term82 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561319 _91244 _91249 f x y)). Qed.
Lemma lem3561321 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561322 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term93 _91244 _91249 f x) = (term94 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561321 _91249) (@lem3561320 _91244 _91249 f x)). Qed.
Lemma lem3561323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561324 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term95 _91244 _91249 f x) = (term96 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561323) (@lem3561322 _91244 _91249 f x)). Qed.
Lemma lem3561325 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term87 _91244 _91249 f x y) = (term24 _91244 _91249 f x y).
Proof. exact (eq_refl (term87 _91244 _91249 f x y)). Qed.
Lemma lem3561326 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term97 _91244 _91249 f x) = (term34 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561325 _91244 _91249 f x y)). Qed.
Lemma lem3561327 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561328 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term98 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561327 _91249) (@lem3561326 _91244 _91249 f x)). Qed.
Lemma lem3561329 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term81 _91244 _91249 f x) = (term99 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561324 _91244 _91249 f x) (@lem3561328 _91244 _91249 f x)). Qed.
Lemma lem3561330 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : ((term80 _91244 _91249 f x) = (term81 _91244 _91249 f x)) = ((term56 _91244 _91249 f x) = (term99 _91244 _91249 f x)).
Proof. exact (MK_COMB (@lem3561318 _91244 _91249 f x) (@lem3561329 _91244 _91249 f x)). Qed.
Lemma lem3561331 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term56 _91244 _91249 f x) = (term99 _91244 _91249 f x).
Proof. exact (EQ_MP (@lem3561330 _91244 _91249 f x) (@lem3561308 _91244 _91249 f x)). Qed.
Lemma lem3561428 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term64 _91244 _91249 f) = (term100 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561331 _91244 _91249 f x)). Qed.
Lemma lem3561429 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561430 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term65 _91244 _91249 f) = (term101 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561429 _91249) (@lem3561428 _91244 _91249 f)). Qed.
Lemma lem3561432 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3561433 {_91249 : Type'} (P : _91249 -> Prop) (Q : _91249 -> Prop) : (term78 _91249 P Q) = (term79 _91249 P Q).
Proof. exact (@lem3561432 _91249 P Q). Qed.
Lemma lem3561434 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term102 _91244 _91249 f) = (term103 _91244 _91249 f).
Proof. exact (@lem3561433 _91249 (term104 _91244 _91249 f) (term43 _91244 _91249 f)). Qed.
Lemma lem3561435 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term105 _91244 _91249 f x) = (term94 _91244 _91249 f x).
Proof. exact (eq_refl (term105 _91244 _91249 f x)). Qed.
Lemma lem3561436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561437 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term106 _91244 _91249 f x) = (term96 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561436) (@lem3561435 _91244 _91249 f x)). Qed.
Lemma lem3561438 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term107 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (eq_refl (term107 _91244 _91249 f x)). Qed.
Lemma lem3561439 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term108 _91244 _91249 f x) = (term99 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561437 _91244 _91249 f x) (@lem3561438 _91244 _91249 f x)). Qed.
Lemma lem3561440 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term109 _91244 _91249 f) = (term100 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561439 _91244 _91249 f x)). Qed.
Lemma lem3561441 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561442 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term102 _91244 _91249 f) = (term101 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561441 _91249) (@lem3561440 _91244 _91249 f)). Qed.
Lemma lem3561443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561444 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term110 _91244 _91249 f) = (term111 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561443) (@lem3561442 _91244 _91249 f)). Qed.
Lemma lem3561445 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term105 _91244 _91249 f x) = (term94 _91244 _91249 f x).
Proof. exact (eq_refl (term105 _91244 _91249 f x)). Qed.
Lemma lem3561446 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term112 _91244 _91249 f) = (term104 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561445 _91244 _91249 f x)). Qed.
Lemma lem3561447 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561448 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term113 _91244 _91249 f) = (term114 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561447 _91249) (@lem3561446 _91244 _91249 f)). Qed.
Lemma lem3561449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561450 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term115 _91244 _91249 f) = (term116 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561449) (@lem3561448 _91244 _91249 f)). Qed.
Lemma lem3561451 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term107 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (eq_refl (term107 _91244 _91249 f x)). Qed.
Lemma lem3561452 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term117 _91244 _91249 f) = (term43 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561451 _91244 _91249 f x)). Qed.
Lemma lem3561453 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561454 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term118 _91244 _91249 f) = (term44 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561453 _91249) (@lem3561452 _91244 _91249 f)). Qed.
Lemma lem3561455 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term103 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561450 _91244 _91249 f) (@lem3561454 _91244 _91249 f)). Qed.
Lemma lem3561456 {_91244 _91249 : Type'} (f : _91249 -> _91244) : ((term102 _91244 _91249 f) = (term103 _91244 _91249 f)) = ((term101 _91244 _91249 f) = (term119 _91244 _91249 f)).
Proof. exact (MK_COMB (@lem3561444 _91244 _91249 f) (@lem3561455 _91244 _91249 f)). Qed.
Lemma lem3561457 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term101 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (EQ_MP (@lem3561456 _91244 _91249 f) (@lem3561434 _91244 _91249 f)). Qed.
Lemma lem3561562 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term65 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (TRANS (@lem3561430 _91244 _91249 f) (@lem3561457 _91244 _91249 f)). Qed.
Lemma lem3561563 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term67 _91244 _91249 f) = (term67 _91244 _91249 f).
Proof. exact (eq_refl (term67 _91244 _91249 f)). Qed.
Lemma lem3561564 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term69 _91244 _91249 f) = (term120 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561563 _91244 _91249 f) (@lem3561562 _91244 _91249 f)). Qed.
Lemma lem3561565 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term75 _91244 _91249 f) = (term75 _91244 _91249 f).
Proof. exact (eq_refl (term75 _91244 _91249 f)). Qed.
Lemma lem3561566 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term77 _91244 _91249 f) = (term121 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561565 _91244 _91249 f) (@lem3561564 _91244 _91249 f)). Qed.
Lemma lem3561568 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3561569 {_91249 : Type'} (P : Prop) (Q : _91249 -> Prop) : (term122 _91249 P Q) = (term123 _91249 P Q).
Proof. exact (@lem3561568 _91249 P Q). Qed.
Lemma lem3561570 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term124 _91244 _91249 f) = (term125 _91244 _91249 f).
Proof. exact (@lem3561569 _91249 (term44 _91244 _91249 f) (term62 _91244 _91249 f)). Qed.
Lemma lem3561571 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term126 _91244 _91249 f x) = (term54 _91244 _91249 f x).
Proof. exact (eq_refl (term126 _91244 _91249 f x)). Qed.
Lemma lem3561572 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term127 _91244 _91249 f) = (term62 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561571 _91244 _91249 f x)). Qed.
Lemma lem3561573 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561574 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term128 _91244 _91249 f) = (term63 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561573 _91249) (@lem3561572 _91244 _91249 f)). Qed.
Lemma lem3561575 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term71 _91244 _91249 f) = (term71 _91244 _91249 f).
Proof. exact (eq_refl (term71 _91244 _91249 f)). Qed.
Lemma lem3561576 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term124 _91244 _91249 f) = (term73 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561575 _91244 _91249 f) (@lem3561574 _91244 _91249 f)). Qed.
Lemma lem3561577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561578 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term129 _91244 _91249 f) = (term130 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561577) (@lem3561576 _91244 _91249 f)). Qed.
Lemma lem3561579 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term126 _91244 _91249 f x) = (term54 _91244 _91249 f x).
Proof. exact (eq_refl (term126 _91244 _91249 f x)). Qed.
Lemma lem3561580 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term71 _91244 _91249 f) = (term71 _91244 _91249 f).
Proof. exact (eq_refl (term71 _91244 _91249 f)). Qed.
Lemma lem3561581 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term131 _91244 _91249 f x) = (term132 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561580 _91244 _91249 f) (@lem3561579 _91244 _91249 f x)). Qed.
Lemma lem3561582 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term133 _91244 _91249 f) = (term134 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561581 _91244 _91249 f x)). Qed.
Lemma lem3561583 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561584 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term125 _91244 _91249 f) = (term135 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561583 _91249) (@lem3561582 _91244 _91249 f)). Qed.
Lemma lem3561585 {_91244 _91249 : Type'} (f : _91249 -> _91244) : ((term124 _91244 _91249 f) = (term125 _91244 _91249 f)) = ((term73 _91244 _91249 f) = (term135 _91244 _91249 f)).
Proof. exact (MK_COMB (@lem3561578 _91244 _91249 f) (@lem3561584 _91244 _91249 f)). Qed.
Lemma lem3561586 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term73 _91244 _91249 f) = (term135 _91244 _91249 f).
Proof. exact (EQ_MP (@lem3561585 _91244 _91249 f) (@lem3561570 _91244 _91249 f)). Qed.
Lemma lem3561588 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3561589 {_91249 : Type'} (P : Prop) (Q : _91249 -> Prop) : (term122 _91249 P Q) = (term123 _91249 P Q).
Proof. exact (@lem3561588 _91249 P Q). Qed.
Lemma lem3561590 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term136 _91244 _91249 f x) = (term137 _91244 _91249 f x).
Proof. exact (@lem3561589 _91249 (term44 _91244 _91249 f) (term53 _91244 _91249 f x)). Qed.
Lemma lem3561591 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term138 _91244 _91249 f x y) = (term46 _91244 _91249 f x y).
Proof. exact (eq_refl (term138 _91244 _91249 f x y)). Qed.
Lemma lem3561592 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term139 _91244 _91249 f x) = (term53 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561591 _91244 _91249 f x y)). Qed.
Lemma lem3561593 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561594 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term140 _91244 _91249 f x) = (term54 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561593 _91249) (@lem3561592 _91244 _91249 f x)). Qed.
Lemma lem3561595 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term71 _91244 _91249 f) = (term71 _91244 _91249 f).
Proof. exact (eq_refl (term71 _91244 _91249 f)). Qed.
Lemma lem3561596 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term136 _91244 _91249 f x) = (term132 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561595 _91244 _91249 f) (@lem3561594 _91244 _91249 f x)). Qed.
Lemma lem3561597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561598 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term141 _91244 _91249 f x) = (term142 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561597) (@lem3561596 _91244 _91249 f x)). Qed.
Lemma lem3561599 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term138 _91244 _91249 f x y) = (term46 _91244 _91249 f x y).
Proof. exact (eq_refl (term138 _91244 _91249 f x y)). Qed.
Lemma lem3561600 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term71 _91244 _91249 f) = (term71 _91244 _91249 f).
Proof. exact (eq_refl (term71 _91244 _91249 f)). Qed.
Lemma lem3561601 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term143 _91244 _91249 f x y) = (term144 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561600 _91244 _91249 f) (@lem3561599 _91244 _91249 f x y)). Qed.
Lemma lem3561602 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term145 _91244 _91249 f x) = (term146 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561601 _91244 _91249 f x y)). Qed.
Lemma lem3561603 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561604 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term137 _91244 _91249 f x) = (term147 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561603 _91249) (@lem3561602 _91244 _91249 f x)). Qed.
Lemma lem3561605 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : ((term136 _91244 _91249 f x) = (term137 _91244 _91249 f x)) = ((term132 _91244 _91249 f x) = (term147 _91244 _91249 f x)).
Proof. exact (MK_COMB (@lem3561598 _91244 _91249 f x) (@lem3561604 _91244 _91249 f x)). Qed.
Lemma lem3561606 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term132 _91244 _91249 f x) = (term147 _91244 _91249 f x).
Proof. exact (EQ_MP (@lem3561605 _91244 _91249 f x) (@lem3561590 _91244 _91249 f x)). Qed.
Lemma lem3561607 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term134 _91244 _91249 f) = (term148 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561606 _91244 _91249 f x)). Qed.
Lemma lem3561608 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561609 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term135 _91244 _91249 f) = (term149 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561608 _91249) (@lem3561607 _91244 _91249 f)). Qed.
Lemma lem3561610 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term73 _91244 _91249 f) = (term149 _91244 _91249 f).
Proof. exact (TRANS (@lem3561586 _91244 _91249 f) (@lem3561609 _91244 _91249 f)). Qed.
Lemma lem3561611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3561612 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term75 _91244 _91249 f) = (term150 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561611) (@lem3561610 _91244 _91249 f)). Qed.
Lemma lem3561614 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3561615 {_91249 : Type'} (P : _91249 -> Prop) (Q : Prop) : (term151 _91249 P Q) = (term152 _91249 P Q).
Proof. exact (@lem3561614 _91249 P Q). Qed.
Lemma lem3561616 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term153 _91244 _91249 f) = (term154 _91244 _91249 f).
Proof. exact (@lem3561615 _91249 (term41 _91244 _91249 f) (term119 _91244 _91249 f)). Qed.
Lemma lem3561617 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term155 _91244 _91249 f x) = (term33 _91244 _91249 f x).
Proof. exact (eq_refl (term155 _91244 _91249 f x)). Qed.
Lemma lem3561618 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term156 _91244 _91249 f) = (term41 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561617 _91244 _91249 f x)). Qed.
Lemma lem3561619 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561620 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term157 _91244 _91249 f) = (term42 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561619 _91249) (@lem3561618 _91244 _91249 f)). Qed.
Lemma lem3561621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561622 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term158 _91244 _91249 f) = (term67 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561621) (@lem3561620 _91244 _91249 f)). Qed.
Lemma lem3561623 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term119 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (eq_refl (term119 _91244 _91249 f)). Qed.
Lemma lem3561624 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term153 _91244 _91249 f) = (term120 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561622 _91244 _91249 f) (@lem3561623 _91244 _91249 f)). Qed.
Lemma lem3561625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561626 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term159 _91244 _91249 f) = (term160 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561625) (@lem3561624 _91244 _91249 f)). Qed.
Lemma lem3561627 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term155 _91244 _91249 f x) = (term33 _91244 _91249 f x).
Proof. exact (eq_refl (term155 _91244 _91249 f x)). Qed.
Lemma lem3561628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561629 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term161 _91244 _91249 f x) = (term162 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561628) (@lem3561627 _91244 _91249 f x)). Qed.
Lemma lem3561630 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term119 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (eq_refl (term119 _91244 _91249 f)). Qed.
Lemma lem3561631 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term163 _91244 _91249 x f) = (term164 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561629 _91244 _91249 f x) (@lem3561630 _91244 _91249 f)). Qed.
Lemma lem3561632 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term165 _91244 _91249 f) = (term166 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561631 _91244 _91249 x f)). Qed.
Lemma lem3561633 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561634 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term154 _91244 _91249 f) = (term167 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561633 _91249) (@lem3561632 _91244 _91249 f)). Qed.
Lemma lem3561635 {_91244 _91249 : Type'} (f : _91249 -> _91244) : ((term153 _91244 _91249 f) = (term154 _91244 _91249 f)) = ((term120 _91244 _91249 f) = (term167 _91244 _91249 f)).
Proof. exact (MK_COMB (@lem3561626 _91244 _91249 f) (@lem3561634 _91244 _91249 f)). Qed.
Lemma lem3561636 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term120 _91244 _91249 f) = (term167 _91244 _91249 f).
Proof. exact (EQ_MP (@lem3561635 _91244 _91249 f) (@lem3561616 _91244 _91249 f)). Qed.
Lemma lem3561638 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3561639 {_91249 : Type'} (P : _91249 -> Prop) (Q : Prop) : (term151 _91249 P Q) = (term152 _91249 P Q).
Proof. exact (@lem3561638 _91249 P Q). Qed.
Lemma lem3561640 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term168 _91244 _91249 x f) = (term169 _91244 _91249 x f).
Proof. exact (@lem3561639 _91249 (term32 _91244 _91249 f x) (term119 _91244 _91249 f)). Qed.
Lemma lem3561641 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term170 _91244 _91249 f x y) = (term23 _91244 _91249 f x y).
Proof. exact (eq_refl (term170 _91244 _91249 f x y)). Qed.
Lemma lem3561642 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term171 _91244 _91249 f x) = (term32 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561641 _91244 _91249 f x y)). Qed.
Lemma lem3561643 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561644 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term172 _91244 _91249 f x) = (term33 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561643 _91249) (@lem3561642 _91244 _91249 f x)). Qed.
Lemma lem3561645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561646 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term173 _91244 _91249 f x) = (term162 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561645) (@lem3561644 _91244 _91249 f x)). Qed.
Lemma lem3561647 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term119 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (eq_refl (term119 _91244 _91249 f)). Qed.
Lemma lem3561648 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term168 _91244 _91249 x f) = (term164 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561646 _91244 _91249 f x) (@lem3561647 _91244 _91249 f)). Qed.
Lemma lem3561649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561650 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term174 _91244 _91249 x f) = (term175 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561649) (@lem3561648 _91244 _91249 x f)). Qed.
Lemma lem3561651 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term170 _91244 _91249 f x y) = (term23 _91244 _91249 f x y).
Proof. exact (eq_refl (term170 _91244 _91249 f x y)). Qed.
Lemma lem3561652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561653 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term176 _91244 _91249 f x y) = (term177 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561652) (@lem3561651 _91244 _91249 f x y)). Qed.
Lemma lem3561654 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term119 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (eq_refl (term119 _91244 _91249 f)). Qed.
Lemma lem3561655 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) : (term178 _91244 _91249 x y f) = (term179 _91244 _91249 x y f).
Proof. exact (MK_COMB (@lem3561653 _91244 _91249 f x y) (@lem3561654 _91244 _91249 f)). Qed.
Lemma lem3561656 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term180 _91244 _91249 x f) = (term181 _91244 _91249 x f).
Proof. exact (fun_ext (fun y : _91249 => @lem3561655 _91244 _91249 x y f)). Qed.
Lemma lem3561657 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561658 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term169 _91244 _91249 x f) = (term182 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561657 _91249) (@lem3561656 _91244 _91249 x f)). Qed.
Lemma lem3561659 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : ((term168 _91244 _91249 x f) = (term169 _91244 _91249 x f)) = ((term164 _91244 _91249 x f) = (term182 _91244 _91249 x f)).
Proof. exact (MK_COMB (@lem3561650 _91244 _91249 x f) (@lem3561658 _91244 _91249 x f)). Qed.
Lemma lem3561660 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term164 _91244 _91249 x f) = (term182 _91244 _91249 x f).
Proof. exact (EQ_MP (@lem3561659 _91244 _91249 x f) (@lem3561640 _91244 _91249 x f)). Qed.
Lemma lem3561661 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term166 _91244 _91249 f) = (term183 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561660 _91244 _91249 x f)). Qed.
Lemma lem3561662 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561663 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term167 _91244 _91249 f) = (term184 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561662 _91249) (@lem3561661 _91244 _91249 f)). Qed.
Lemma lem3561664 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term120 _91244 _91249 f) = (term184 _91244 _91249 f).
Proof. exact (TRANS (@lem3561636 _91244 _91249 f) (@lem3561663 _91244 _91249 f)). Qed.
Lemma lem3561665 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term121 _91244 _91249 f) = (term185 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561612 _91244 _91249 f) (@lem3561664 _91244 _91249 f)). Qed.
Lemma lem3561667 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3561668 {_91249 : Type'} (P : _91249 -> Prop) (Q : _91249 -> Prop) : (term186 _91249 P Q) = (term187 _91249 P Q).
Proof. exact (@lem3561667 _91249 P Q). Qed.
Lemma lem3561669 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term188 _91244 _91249 f) = (term189 _91244 _91249 f).
Proof. exact (@lem3561668 _91249 (term148 _91244 _91249 f) (term183 _91244 _91249 f)). Qed.
Lemma lem3561670 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term190 _91244 _91249 f x) = (term147 _91244 _91249 f x).
Proof. exact (eq_refl (term190 _91244 _91249 f x)). Qed.
Lemma lem3561671 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term191 _91244 _91249 f) = (term148 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561670 _91244 _91249 f x)). Qed.
Lemma lem3561672 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561673 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term192 _91244 _91249 f) = (term149 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561672 _91249) (@lem3561671 _91244 _91249 f)). Qed.
Lemma lem3561674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3561675 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term193 _91244 _91249 f) = (term150 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561674) (@lem3561673 _91244 _91249 f)). Qed.
Lemma lem3561676 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term194 _91244 _91249 f x) = (term182 _91244 _91249 x f).
Proof. exact (eq_refl (term194 _91244 _91249 f x)). Qed.
Lemma lem3561677 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term195 _91244 _91249 f) = (term183 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561676 _91244 _91249 x f)). Qed.
Lemma lem3561678 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561679 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term196 _91244 _91249 f) = (term184 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561678 _91249) (@lem3561677 _91244 _91249 f)). Qed.
Lemma lem3561680 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term188 _91244 _91249 f) = (term185 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561675 _91244 _91249 f) (@lem3561679 _91244 _91249 f)). Qed.
Lemma lem3561681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561682 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term197 _91244 _91249 f) = (term198 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561681) (@lem3561680 _91244 _91249 f)). Qed.
Lemma lem3561683 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term190 _91244 _91249 f x) = (term147 _91244 _91249 f x).
Proof. exact (eq_refl (term190 _91244 _91249 f x)). Qed.
Lemma lem3561684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3561685 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term199 _91244 _91249 f x) = (term200 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561684) (@lem3561683 _91244 _91249 f x)). Qed.
Lemma lem3561686 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term194 _91244 _91249 f x) = (term182 _91244 _91249 x f).
Proof. exact (eq_refl (term194 _91244 _91249 f x)). Qed.
Lemma lem3561687 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term201 _91244 _91249 f x) = (term202 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561685 _91244 _91249 f x) (@lem3561686 _91244 _91249 x f)). Qed.
Lemma lem3561688 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term203 _91244 _91249 f) = (term204 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561687 _91244 _91249 x f)). Qed.
Lemma lem3561689 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561690 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term189 _91244 _91249 f) = (term205 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561689 _91249) (@lem3561688 _91244 _91249 f)). Qed.
Lemma lem3561691 {_91244 _91249 : Type'} (f : _91249 -> _91244) : ((term188 _91244 _91249 f) = (term189 _91244 _91249 f)) = ((term185 _91244 _91249 f) = (term205 _91244 _91249 f)).
Proof. exact (MK_COMB (@lem3561682 _91244 _91249 f) (@lem3561690 _91244 _91249 f)). Qed.
Lemma lem3561692 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term185 _91244 _91249 f) = (term205 _91244 _91249 f).
Proof. exact (EQ_MP (@lem3561691 _91244 _91249 f) (@lem3561669 _91244 _91249 f)). Qed.
Lemma lem3561694 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3561695 {_91249 : Type'} (P : _91249 -> Prop) (Q : _91249 -> Prop) : (term186 _91249 P Q) = (term187 _91249 P Q).
Proof. exact (@lem3561694 _91249 P Q). Qed.
Lemma lem3561696 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term206 _91244 _91249 x f) = (term207 _91244 _91249 x f).
Proof. exact (@lem3561695 _91249 (term146 _91244 _91249 f x) (term181 _91244 _91249 x f)). Qed.
Lemma lem3561697 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term208 _91244 _91249 f x y) = (term144 _91244 _91249 f x y).
Proof. exact (eq_refl (term208 _91244 _91249 f x y)). Qed.
Lemma lem3561698 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term209 _91244 _91249 f x) = (term146 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561697 _91244 _91249 f x y)). Qed.
Lemma lem3561699 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561700 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term210 _91244 _91249 f x) = (term147 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561699 _91249) (@lem3561698 _91244 _91249 f x)). Qed.
Lemma lem3561701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3561702 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term211 _91244 _91249 f x) = (term200 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561701) (@lem3561700 _91244 _91249 f x)). Qed.
Lemma lem3561703 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) : (term212 _91244 _91249 x f y) = (term179 _91244 _91249 x y f).
Proof. exact (eq_refl (term212 _91244 _91249 x f y)). Qed.
Lemma lem3561704 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term213 _91244 _91249 x f) = (term181 _91244 _91249 x f).
Proof. exact (fun_ext (fun y : _91249 => @lem3561703 _91244 _91249 x y f)). Qed.
Lemma lem3561705 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561706 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term214 _91244 _91249 x f) = (term182 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561705 _91249) (@lem3561704 _91244 _91249 x f)). Qed.
Lemma lem3561707 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term206 _91244 _91249 x f) = (term202 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561702 _91244 _91249 f x) (@lem3561706 _91244 _91249 x f)). Qed.
Lemma lem3561708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3561709 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term215 _91244 _91249 x f) = (term216 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561708) (@lem3561707 _91244 _91249 x f)). Qed.
Lemma lem3561710 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term208 _91244 _91249 f x y) = (term144 _91244 _91249 f x y).
Proof. exact (eq_refl (term208 _91244 _91249 f x y)). Qed.
Lemma lem3561711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3561712 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term217 _91244 _91249 f x y) = (term218 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561711) (@lem3561710 _91244 _91249 f x y)). Qed.
Lemma lem3561713 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) : (term212 _91244 _91249 x f y) = (term179 _91244 _91249 x y f).
Proof. exact (eq_refl (term212 _91244 _91249 x f y)). Qed.
Lemma lem3561714 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) : (term219 _91244 _91249 x f y) = (term220 _91244 _91249 x y f).
Proof. exact (MK_COMB (@lem3561712 _91244 _91249 f x y) (@lem3561713 _91244 _91249 x y f)). Qed.
Lemma lem3561715 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term221 _91244 _91249 x f) = (term222 _91244 _91249 x f).
Proof. exact (fun_ext (fun y : _91249 => @lem3561714 _91244 _91249 x y f)). Qed.
Lemma lem3561716 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561717 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term207 _91244 _91249 x f) = (term223 _91244 _91249 x f).
Proof. exact (MK_COMB (@lem3561716 _91249) (@lem3561715 _91244 _91249 x f)). Qed.
Lemma lem3561718 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : ((term206 _91244 _91249 x f) = (term207 _91244 _91249 x f)) = ((term202 _91244 _91249 x f) = (term223 _91244 _91249 x f)).
Proof. exact (MK_COMB (@lem3561709 _91244 _91249 x f) (@lem3561717 _91244 _91249 x f)). Qed.
Lemma lem3561719 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) : (term202 _91244 _91249 x f) = (term223 _91244 _91249 x f).
Proof. exact (EQ_MP (@lem3561718 _91244 _91249 x f) (@lem3561696 _91244 _91249 x f)). Qed.
Lemma lem3561720 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term204 _91244 _91249 f) = (term224 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561719 _91244 _91249 x f)). Qed.
Lemma lem3561721 {_91249 : Type'} : (@ex _91249) = (@ex _91249).
Proof. exact (eq_refl (@ex _91249)). Qed.
Lemma lem3561722 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term205 _91244 _91249 f) = (term225 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561721 _91249) (@lem3561720 _91244 _91249 f)). Qed.
Lemma lem3561723 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term185 _91244 _91249 f) = (term225 _91244 _91249 f).
Proof. exact (TRANS (@lem3561692 _91244 _91249 f) (@lem3561722 _91244 _91249 f)). Qed.
Lemma lem3561724 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term121 _91244 _91249 f) = (term225 _91244 _91249 f).
Proof. exact (TRANS (@lem3561665 _91244 _91249 f) (@lem3561723 _91244 _91249 f)). Qed.
Lemma lem3561725 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term77 _91244 _91249 f) = (term225 _91244 _91249 f).
Proof. exact (TRANS (@lem3561566 _91244 _91249 f) (@lem3561724 _91244 _91249 f)). Qed.
Lemma lem3561726 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term21 _91244 _91249 f) = (term225 _91244 _91249 f).
Proof. exact (TRANS (@lem3561144 _91244 _91249 f) (@lem3561725 _91244 _91249 f)). Qed.
Lemma lem3561727 {_91244 _91249 : Type'} (f : _91249 -> _91244) (h1 : term21 _91244 _91249 f) : term225 _91244 _91249 f.
Proof. exact (EQ_MP (@lem3561726 _91244 _91249 f) (@lem3561041 _91244 _91249 f h1)). Qed.
Lemma lem3561728 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (h1 : term223 _91244 _91249 x f) : term223 _91244 _91249 x f.
Proof. exact (h1). Qed.
Lemma lem3561729 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term220 _91244 _91249 x y f) : term220 _91244 _91249 x y f.
Proof. exact (h1). Qed.
Lemma lem3561748 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term24 _91244 _91249 f x y) = (term24 _91244 _91249 f x y).
Proof. exact (eq_refl (term24 _91244 _91249 f x y)). Qed.
Lemma lem3561749 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term34 _91244 _91249 f x) = (term34 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561748 _91244 _91249 f x y)). Qed.
Lemma lem3561750 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561751 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term35 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561750 _91249) (@lem3561749 _91244 _91249 f x)). Qed.
Lemma lem3561752 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term43 _91244 _91249 f) = (term43 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561751 _91244 _91249 f x)). Qed.
Lemma lem3561753 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561754 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term44 _91244 _91249 f) = (term44 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561753 _91249) (@lem3561752 _91244 _91249 f)). Qed.
Lemma lem3561773 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term84 _91244 _91249 f x y) = (term84 _91244 _91249 f x y).
Proof. exact (eq_refl (term84 _91244 _91249 f x y)). Qed.
Lemma lem3561774 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term82 _91244 _91249 f x) = (term82 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561773 _91244 _91249 f x y)). Qed.
Lemma lem3561775 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561776 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term94 _91244 _91249 f x) = (term94 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561775 _91249) (@lem3561774 _91244 _91249 f x)). Qed.
Lemma lem3561777 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term104 _91244 _91249 f) = (term104 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561776 _91244 _91249 f x)). Qed.
Lemma lem3561778 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561779 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term114 _91244 _91249 f) = (term114 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561778 _91249) (@lem3561777 _91244 _91249 f)). Qed.
Lemma lem3561780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561781 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term116 _91244 _91249 f) = (term116 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561780) (@lem3561779 _91244 _91249 f)). Qed.
Lemma lem3561782 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term119 _91244 _91249 f) = (term119 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561781 _91244 _91249 f) (@lem3561754 _91244 _91249 f)). Qed.
Lemma lem3561803 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term177 _91244 _91249 f x y) = (term177 _91244 _91249 f x y).
Proof. exact (eq_refl (term177 _91244 _91249 f x y)). Qed.
Lemma lem3561804 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) : (term179 _91244 _91249 x y f) = (term179 _91244 _91249 x y f).
Proof. exact (MK_COMB (@lem3561803 _91244 _91249 f x y) (@lem3561782 _91244 _91249 f)). Qed.
Lemma lem3561845 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term46 _91244 _91249 f x y) = (term46 _91244 _91249 f x y).
Proof. exact (eq_refl (term46 _91244 _91249 f x y)). Qed.
Lemma lem3561864 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term24 _91244 _91249 f x y) = (term24 _91244 _91249 f x y).
Proof. exact (eq_refl (term24 _91244 _91249 f x y)). Qed.
Lemma lem3561865 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term34 _91244 _91249 f x) = (term34 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561864 _91244 _91249 f x y)). Qed.
Lemma lem3561866 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561867 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term35 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561866 _91249) (@lem3561865 _91244 _91249 f x)). Qed.
Lemma lem3561868 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term43 _91244 _91249 f) = (term43 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561867 _91244 _91249 f x)). Qed.
Lemma lem3561869 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561870 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term44 _91244 _91249 f) = (term44 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561869 _91249) (@lem3561868 _91244 _91249 f)). Qed.
Lemma lem3561871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3561872 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term71 _91244 _91249 f) = (term71 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561871) (@lem3561870 _91244 _91249 f)). Qed.
Lemma lem3561873 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term144 _91244 _91249 f x y) = (term144 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561872 _91244 _91249 f) (@lem3561845 _91244 _91249 f x y)). Qed.
Lemma lem3561874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3561875 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term218 _91244 _91249 f x y) = (term218 _91244 _91249 f x y).
Proof. exact (MK_COMB (@lem3561874) (@lem3561873 _91244 _91249 f x y)). Qed.
Lemma lem3561876 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) : (term220 _91244 _91249 x y f) = (term220 _91244 _91249 x y f).
Proof. exact (MK_COMB (@lem3561875 _91244 _91249 f x y) (@lem3561804 _91244 _91249 x y f)). Qed.
Lemma lem3561877 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term220 _91244 _91249 x y f) : term220 _91244 _91249 x y f.
Proof. exact (EQ_MP (@lem3561876 _91244 _91249 x y f) (@lem3561729 _91244 _91249 x y f h1)). Qed.
Lemma lem3561878 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term144 _91244 _91249 f x y.
Proof. exact (h1). Qed.
Lemma lem3561879 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term179 _91244 _91249 x y f.
Proof. exact (h1). Qed.
Lemma lem3561880 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term46 _91244 _91249 f x y.
Proof. exact (proj2 (@lem3561878 _91244 _91249 f x y h1)). Qed.
Lemma lem3561881 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term44 _91244 _91249 f.
Proof. exact (proj1 (@lem3561878 _91244 _91249 f x y h1)). Qed.
Lemma lem3561882 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term226 _91244 _91249 f x y.
Proof. exact (proj2 (@lem3561880 _91244 _91249 f x y h1)). Qed.
Lemma lem3561883 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term227 _91244 _91249 f x y.
Proof. exact (proj1 (@lem3561880 _91244 _91249 f x y h1)). Qed.
Lemma lem3561890 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term119 _91244 _91249 f.
Proof. exact (proj2 (@lem3561879 _91244 _91249 x y f h1)). Qed.
Lemma lem3561891 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term23 _91244 _91249 f x y.
Proof. exact (proj1 (@lem3561879 _91244 _91249 x y f h1)). Qed.
Lemma lem3561892 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term44 _91244 _91249 f.
Proof. exact (proj2 (@lem3561890 _91244 _91249 x y f h1)). Qed.
Lemma lem3561915 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) : term228 _91244 _91249 x f y.
Proof. exact (h1). Qed.
Lemma lem3561919 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3561939 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) : term228 _91244 _91249 x f y.
Proof. exact (h1). Qed.
Lemma lem3561943 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3561951 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term24 _91244 _91249 f x y) = (term24 _91244 _91249 f x y).
Proof. exact (eq_refl (term24 _91244 _91249 f x y)). Qed.
Lemma lem3561952 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term34 _91244 _91249 f x) = (term34 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3561951 _91244 _91249 f x y)). Qed.
Lemma lem3561953 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561954 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term35 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3561953 _91249) (@lem3561952 _91244 _91249 f x)). Qed.
Lemma lem3561955 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term43 _91244 _91249 f) = (term43 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3561954 _91244 _91249 f x)). Qed.
Lemma lem3561956 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3561958 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term44 _91244 _91249 f) = (term44 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3561956 _91249) (@lem3561955 _91244 _91249 f)). Qed.
Lemma lem3561959 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term44 _91244 _91249 f.
Proof. exact (EQ_MP (@lem3561958 _91244 _91249 f) (@lem3561881 _91244 _91249 f x y h1)). Qed.
Lemma lem3561963 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) : term229 _91249 x y.
Proof. exact (h1). Qed.
Lemma lem3561967 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3561987 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) : term229 _91249 x y.
Proof. exact (h1). Qed.
Lemma lem3561991 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3562015 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) : (term24 _91244 _91249 f x y) = (term24 _91244 _91249 f x y).
Proof. exact (eq_refl (term24 _91244 _91249 f x y)). Qed.
Lemma lem3562016 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term34 _91244 _91249 f x) = (term34 _91244 _91249 f x).
Proof. exact (fun_ext (fun y : _91249 => @lem3562015 _91244 _91249 f x y)). Qed.
Lemma lem3562017 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3562018 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) : (term35 _91244 _91249 f x) = (term35 _91244 _91249 f x).
Proof. exact (MK_COMB (@lem3562017 _91249) (@lem3562016 _91244 _91249 f x)). Qed.
Lemma lem3562019 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term43 _91244 _91249 f) = (term43 _91244 _91249 f).
Proof. exact (fun_ext (fun x : _91249 => @lem3562018 _91244 _91249 f x)). Qed.
Lemma lem3562020 {_91249 : Type'} : (@all _91249) = (@all _91249).
Proof. exact (eq_refl (@all _91249)). Qed.
Lemma lem3562022 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term44 _91244 _91249 f) = (term44 _91244 _91249 f).
Proof. exact (MK_COMB (@lem3562020 _91249) (@lem3562019 _91244 _91249 f)). Qed.
Lemma lem3562023 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term44 _91244 _91249 f.
Proof. exact (EQ_MP (@lem3562022 _91244 _91249 f) (@lem3561892 _91244 _91249 x y f h1)). Qed.
Lemma lem3562044 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term107 _91244 _91249 f _38196.
Proof. exact (@lem3561959 _91244 _91249 f x y h1 _38196). Qed.
Lemma lem3562045 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38196 : _91249) : (term107 _91244 _91249 f _38196) = (term35 _91244 _91249 f _38196).
Proof. exact (eq_refl (term107 _91244 _91249 f _38196)). Qed.
Lemma lem3562046 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term35 _91244 _91249 f _38196.
Proof. exact (EQ_MP (@lem3562045 _91244 _91249 f _38196) (@lem3562044 _91244 _91249 _38196 f x y h1)). Qed.
Lemma lem3562047 {_91244 _91249 : Type'} (_38196 : _91249) (_38197 : _91249) (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term87 _91244 _91249 f _38196 _38197.
Proof. exact (@lem3562046 _91244 _91249 _38196 f x y h1 _38197). Qed.
Lemma lem3562048 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38196 : _91249) (_38197 : _91249) : (term87 _91244 _91249 f _38196 _38197) = (term24 _91244 _91249 f _38196 _38197).
Proof. exact (eq_refl (term87 _91244 _91249 f _38196 _38197)). Qed.
Lemma lem3562062 {_91244 _91249 : Type'} (_38202 : _91249) (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term107 _91244 _91249 f _38202.
Proof. exact (@lem3562023 _91244 _91249 x y f h1 _38202). Qed.
Lemma lem3562063 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38202 : _91249) : (term107 _91244 _91249 f _38202) = (term35 _91244 _91249 f _38202).
Proof. exact (eq_refl (term107 _91244 _91249 f _38202)). Qed.
Lemma lem3562064 {_91244 _91249 : Type'} (_38202 : _91249) (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term35 _91244 _91249 f _38202.
Proof. exact (EQ_MP (@lem3562063 _91244 _91249 f _38202) (@lem3562062 _91244 _91249 _38202 x y f h1)). Qed.
Lemma lem3562065 {_91244 _91249 : Type'} (_38202 : _91249) (_38203 : _91249) (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term87 _91244 _91249 f _38202 _38203.
Proof. exact (@lem3562064 _91244 _91249 _38202 x y f h1 _38203). Qed.
Lemma lem3562066 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38202 : _91249) (_38203 : _91249) : (term87 _91244 _91249 f _38202 _38203) = (term24 _91244 _91249 f _38202 _38203).
Proof. exact (eq_refl (term87 _91244 _91249 f _38202 _38203)). Qed.
Lemma lem3562075 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) : term228 _91244 _91249 x f y.
Proof. exact (h1). Qed.
Lemma lem3562077 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3562085 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) : term228 _91244 _91249 x f y.
Proof. exact (h1). Qed.
Lemma lem3562087 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3562093 {_91244 _91249 : Type'} (_38196 : _91249) (_38197 : _91249) (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term24 _91244 _91249 f _38196 _38197.
Proof. exact (EQ_MP (@lem3562048 _91244 _91249 f _38196 _38197) (@lem3562047 _91244 _91249 _38196 _38197 f x y h1)). Qed.
Lemma lem3562095 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) : term229 _91249 x y.
Proof. exact (h1). Qed.
Lemma lem3562097 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3562105 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) : term229 _91249 x y.
Proof. exact (h1). Qed.
Lemma lem3562107 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3562119 {_91244 _91249 : Type'} (_38202 : _91249) (_38203 : _91249) (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term24 _91244 _91249 f _38202 _38203.
Proof. exact (EQ_MP (@lem3562066 _91244 _91249 f _38202 _38203) (@lem3562065 _91244 _91249 _38202 _38203 x y f h1)). Qed.
Lemma lem3562123 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term229 _91249 x y.
Proof. exact (proj2 (@lem3561891 _91244 _91249 x y f h1)). Qed.
Lemma lem3562152 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : (term230 _91244 _91249 f y) = (term230 _91244 _91249 f y).
Proof. exact (eq_refl (term230 _91244 _91249 f y)). Qed.
Lemma lem3562153 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : x = y) : (term231 _91244 _91249 f y x) = (term232 _91244 _91249 f y).
Proof. exact (MK_COMB (@lem3562152 _91244 _91249 f y) (@lem3562087 _91249 x y h1)). Qed.
Lemma lem3562154 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : (term232 _91244 _91249 f y) = (term233 _91244 _91249 f y).
Proof. exact (eq_refl (term232 _91244 _91249 f y)). Qed.
Lemma lem3562155 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) (x : _91249) : (term234 _91244 _91249 f y x) = (term234 _91244 _91249 f y x).
Proof. exact (eq_refl (term234 _91244 _91249 f y x)). Qed.
Lemma lem3562156 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : ((term231 _91244 _91249 f y x) = (term232 _91244 _91249 f y)) = ((term231 _91244 _91249 f y x) = (term233 _91244 _91249 f y)).
Proof. exact (MK_COMB (@lem3562155 _91244 _91249 f y x) (@lem3562154 _91244 _91249 f y)). Qed.
Lemma lem3562157 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : (term231 _91244 _91249 f y x) = (term228 _91244 _91249 x f y).
Proof. exact (eq_refl (term231 _91244 _91249 f y x)). Qed.
Lemma lem3562158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562159 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : (term234 _91244 _91249 f y x) = (term235 _91244 _91249 x f y).
Proof. exact (MK_COMB (@lem3562158) (@lem3562157 _91244 _91249 x f y)). Qed.
Lemma lem3562160 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : (term233 _91244 _91249 f y) = (term233 _91244 _91249 f y).
Proof. exact (eq_refl (term233 _91244 _91249 f y)). Qed.
Lemma lem3562161 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : ((term231 _91244 _91249 f y x) = (term233 _91244 _91249 f y)) = ((term228 _91244 _91249 x f y) = (term233 _91244 _91249 f y)).
Proof. exact (MK_COMB (@lem3562159 _91244 _91249 x f y) (@lem3562160 _91244 _91249 f y)). Qed.
Lemma lem3562162 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : ((term231 _91244 _91249 f y x) = (term232 _91244 _91249 f y)) = ((term228 _91244 _91249 x f y) = (term233 _91244 _91249 f y)).
Proof. exact (TRANS (@lem3562156 _91244 _91249 x f y) (@lem3562161 _91244 _91249 x f y)). Qed.
Lemma lem3562163 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : x = y) : (term228 _91244 _91249 x f y) = (term233 _91244 _91249 f y).
Proof. exact (EQ_MP (@lem3562162 _91244 _91249 x f y) (@lem3562153 _91244 _91249 f x y h1)). Qed.
Lemma lem3562164 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : term233 _91244 _91249 f y.
Proof. exact (EQ_MP (@lem3562163 _91244 _91249 f x y h2) (@lem3562085 _91244 _91249 x f y h1)). Qed.
Lemma lem3562193 {_91249 : Type'} (y : _91249) : (term236 _91249 y) = (term236 _91249 y).
Proof. exact (eq_refl (term236 _91249 y)). Qed.
Lemma lem3562194 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : x = y) : (term237 _91249 y x) = (term238 _91249 y).
Proof. exact (MK_COMB (@lem3562193 _91249 y) (@lem3562107 _91249 x y h1)). Qed.
Lemma lem3562195 {_91249 : Type'} (y : _91249) : (term238 _91249 y) = (term239 _91249 y).
Proof. exact (eq_refl (term238 _91249 y)). Qed.
Lemma lem3562196 {_91249 : Type'} (y : _91249) (x : _91249) : (term240 _91249 y x) = (term240 _91249 y x).
Proof. exact (eq_refl (term240 _91249 y x)). Qed.
Lemma lem3562197 {_91249 : Type'} (x : _91249) (y : _91249) : ((term237 _91249 y x) = (term238 _91249 y)) = ((term237 _91249 y x) = (term239 _91249 y)).
Proof. exact (MK_COMB (@lem3562196 _91249 y x) (@lem3562195 _91249 y)). Qed.
Lemma lem3562198 {_91249 : Type'} (x : _91249) (y : _91249) : (term237 _91249 y x) = (term229 _91249 x y).
Proof. exact (eq_refl (term237 _91249 y x)). Qed.
Lemma lem3562199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562200 {_91249 : Type'} (x : _91249) (y : _91249) : (term240 _91249 y x) = (term241 _91249 x y).
Proof. exact (MK_COMB (@lem3562199) (@lem3562198 _91249 x y)). Qed.
Lemma lem3562201 {_91249 : Type'} (y : _91249) : (term239 _91249 y) = (term239 _91249 y).
Proof. exact (eq_refl (term239 _91249 y)). Qed.
Lemma lem3562202 {_91249 : Type'} (x : _91249) (y : _91249) : ((term237 _91249 y x) = (term239 _91249 y)) = ((term229 _91249 x y) = (term239 _91249 y)).
Proof. exact (MK_COMB (@lem3562200 _91249 x y) (@lem3562201 _91249 y)). Qed.
Lemma lem3562203 {_91249 : Type'} (x : _91249) (y : _91249) : ((term237 _91249 y x) = (term238 _91249 y)) = ((term229 _91249 x y) = (term239 _91249 y)).
Proof. exact (TRANS (@lem3562197 _91249 x y) (@lem3562202 _91249 x y)). Qed.
Lemma lem3562204 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : x = y) : (term229 _91249 x y) = (term239 _91249 y).
Proof. exact (EQ_MP (@lem3562203 _91249 x y) (@lem3562194 _91249 x y h1)). Qed.
Lemma lem3562205 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : term239 _91249 y.
Proof. exact (EQ_MP (@lem3562204 _91249 x y h2) (@lem3562105 _91249 x y h1)). Qed.
Lemma lem3562219 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3562220 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : term242 _91244 _91249 x f y.
Proof. exact (fun h0 : term228 _91244 _91249 x f y => @lem3562219 _91244 _91249 x f y h1). Qed.
Lemma lem3562222 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562223 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : (term242 _91244 _91249 x f y) = ((f x) = (f y)).
Proof. exact (@lem3562222 ((f x) = (f y))). Qed.
Lemma lem3562224 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (EQ_MP (@lem3562223 _91244 _91249 x f y) (@lem3562220 _91244 _91249 x f y h1)). Qed.
Lemma lem3562227 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3562229 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : (term228 _91244 _91249 x f y) = (term244 _91244 _91249 x f y).
Proof. exact (@lem3562227 ((f x) = (f y))). Qed.
Lemma lem3562232 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) : term244 _91244 _91249 x f y.
Proof. exact (EQ_MP (@lem3562229 _91244 _91249 x f y) (@lem3562075 _91244 _91249 x f y h1)). Qed.
Lemma lem3562235 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (@lem3562232 _91244 _91249 x f y h1 (@lem3562224 _91244 _91249 x f y h2)). Qed.
Lemma lem3562236 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : term245.
Proof. exact (fun h0 : ~ False => @lem3562235 _91244 _91249 x f y h1 h2). Qed.
Lemma lem3562238 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562239 : term245 = False.
Proof. exact (@lem3562238 False). Qed.
Lemma lem3562240 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562239) (@lem3562236 _91244 _91249 x f y h1 h2)). Qed.
Lemma lem3562254 {_91244 : Type'} (x : _91244) : x = x.
Proof. exact (@lem21386 _91244 x). Qed.
Lemma lem3562255 {_91244 : Type'} (x : _91244) : x = x.
Proof. exact (@lem3562254 _91244 x). Qed.
Lemma lem3562256 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : (f y) = (f y).
Proof. exact (@lem3562255 _91244 (f y)). Qed.
Lemma lem3562257 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : term246 _91244 _91249 f y.
Proof. exact (fun h0 : term233 _91244 _91249 f y => @lem3562256 _91244 _91249 f y). Qed.
Lemma lem3562259 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562260 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : (term246 _91244 _91249 f y) = ((f y) = (f y)).
Proof. exact (@lem3562259 ((f y) = (f y))). Qed.
Lemma lem3562261 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : (f y) = (f y).
Proof. exact (EQ_MP (@lem3562260 _91244 _91249 f y) (@lem3562257 _91244 _91249 f y)). Qed.
Lemma lem3562264 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3562266 {_91244 _91249 : Type'} (f : _91249 -> _91244) (y : _91249) : (term233 _91244 _91249 f y) = (term247 _91244 _91249 f y).
Proof. exact (@lem3562264 ((f y) = (f y))). Qed.
Lemma lem3562269 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : term247 _91244 _91249 f y.
Proof. exact (EQ_MP (@lem3562266 _91244 _91249 f y) (@lem3562164 _91244 _91249 f x y h1 h2)). Qed.
Lemma lem3562272 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (@lem3562269 _91244 _91249 f x y h1 h2 (@lem3562261 _91244 _91249 f y)). Qed.
Lemma lem3562273 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : term245.
Proof. exact (fun h0 : ~ False => @lem3562272 _91244 _91249 f x y h1 h2). Qed.
Lemma lem3562275 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562276 : term245 = False.
Proof. exact (@lem3562275 False). Qed.
Lemma lem3562291 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem3562292 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : term242 _91244 _91249 x f y.
Proof. exact (fun h0 : term228 _91244 _91249 x f y => @lem3562291 _91244 _91249 x f y h1). Qed.
Lemma lem3562294 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562295 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : (term242 _91244 _91249 x f y) = ((f x) = (f y)).
Proof. exact (@lem3562294 ((f x) = (f y))). Qed.
Lemma lem3562296 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (EQ_MP (@lem3562295 _91244 _91249 x f y) (@lem3562292 _91244 _91249 x f y h1)). Qed.
Lemma lem3562302 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3562303 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : (term24 _91244 _91249 f _38196 _38197) = (term248 _91244 _91249 _38196 f _38197).
Proof. exact (@lem3562302 (_38196 = _38197) (term228 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562314 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : (term249 _91244 _91249 f _38196 _38197) = (term250 _91244 _91249 _38196 f _38197).
Proof. exact (MK_COMB (@lem3562313) (@lem3562303 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562324 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : (term248 _91244 _91249 _38196 f _38197) = (term248 _91244 _91249 _38196 f _38197).
Proof. exact (eq_refl (term248 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562325 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : ((term24 _91244 _91249 f _38196 _38197) = (term248 _91244 _91249 _38196 f _38197)) = ((term248 _91244 _91249 _38196 f _38197) = (term248 _91244 _91249 _38196 f _38197)).
Proof. exact (MK_COMB (@lem3562314 _91244 _91249 _38196 f _38197) (@lem3562324 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562327 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3562328 (x : Prop) : (x = x) = True.
Proof. exact (@lem3562327 Prop x). Qed.
Lemma lem3562329 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : ((term248 _91244 _91249 _38196 f _38197) = (term248 _91244 _91249 _38196 f _38197)) = True.
Proof. exact (@lem3562328 (term248 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562330 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : ((term24 _91244 _91249 f _38196 _38197) = (term248 _91244 _91249 _38196 f _38197)) = True.
Proof. exact (TRANS (@lem3562325 _91244 _91249 _38196 f _38197) (@lem3562329 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562331 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : True = ((term24 _91244 _91249 f _38196 _38197) = (term248 _91244 _91249 _38196 f _38197)).
Proof. exact (SYM (@lem3562330 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562332 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : (term24 _91244 _91249 f _38196 _38197) = (term248 _91244 _91249 _38196 f _38197).
Proof. exact (EQ_MP (@lem3562331 _91244 _91249 _38196 f _38197) (@lem0)). Qed.
Lemma lem3562333 {_91244 _91249 : Type'} (_38196 : _91249) (_38197 : _91249) (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term248 _91244 _91249 _38196 f _38197.
Proof. exact (EQ_MP (@lem3562332 _91244 _91249 _38196 f _38197) (@lem3562093 _91244 _91249 _38196 _38197 f x y h1)). Qed.
Lemma lem3562335 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3562336 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38196 : _91249) (_38197 : _91249) : (term248 _91244 _91249 _38196 f _38197) = (term252 _91244 _91249 f _38196 _38197).
Proof. exact (@lem3562335 (term228 _91244 _91249 _38196 f _38197) (_38196 = _38197)). Qed.
Lemma lem3562338 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3562339 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : (term253 _91244 _91249 _38196 f _38197) = ((f _38196) = (f _38197)).
Proof. exact (@lem3562338 ((f _38196) = (f _38197))). Qed.
Lemma lem3562340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3562341 {_91244 _91249 : Type'} (_38196 : _91249) (f : _91249 -> _91244) (_38197 : _91249) : (term254 _91244 _91249 _38196 f _38197) = (term255 _91244 _91249 _38196 f _38197).
Proof. exact (MK_COMB (@lem3562340) (@lem3562339 _91244 _91249 _38196 f _38197)). Qed.
Lemma lem3562342 {_91249 : Type'} (_38196 : _91249) (_38197 : _91249) : (_38196 = _38197) = (_38196 = _38197).
Proof. exact (eq_refl (_38196 = _38197)). Qed.
Lemma lem3562343 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38196 : _91249) (_38197 : _91249) : (term252 _91244 _91249 f _38196 _38197) = (term13 _91244 _91249 f _38196 _38197).
Proof. exact (MK_COMB (@lem3562341 _91244 _91249 _38196 f _38197) (@lem3562342 _91249 _38196 _38197)). Qed.
Lemma lem3562344 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38196 : _91249) (_38197 : _91249) : (term248 _91244 _91249 _38196 f _38197) = (term13 _91244 _91249 f _38196 _38197).
Proof. exact (TRANS (@lem3562336 _91244 _91249 f _38196 _38197) (@lem3562343 _91244 _91249 f _38196 _38197)). Qed.
Lemma lem3562347 {_91244 _91249 : Type'} (_38196 : _91249) (_38197 : _91249) (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term13 _91244 _91249 f _38196 _38197.
Proof. exact (EQ_MP (@lem3562344 _91244 _91249 f _38196 _38197) (@lem3562333 _91244 _91249 _38196 _38197 f x y h1)). Qed.
Lemma lem3562348 {_91244 _91249 : Type'} (_38196 : _91249) (_38197 : _91249) (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term13 _91244 _91249 f _38196 _38197.
Proof. exact (@lem3562347 _91244 _91249 _38196 _38197 f x y h1). Qed.
Lemma lem3562349 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : term13 _91244 _91249 f x y.
Proof. exact (@lem3562348 _91244 _91249 x y f x y h1). Qed.
Lemma lem3562352 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term144 _91244 _91249 f x y) (h2 : (f x) = (f y)) : x = y.
Proof. exact (@lem3562349 _91244 _91249 f x y h1 (@lem3562296 _91244 _91249 x f y h2)). Qed.
Lemma lem3562353 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term144 _91244 _91249 f x y) (h2 : (f x) = (f y)) : term256 _91249 x y.
Proof. exact (fun h0 : term229 _91249 x y => @lem3562352 _91244 _91249 x f y h1 h2). Qed.
Lemma lem3562355 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562356 {_91249 : Type'} (x : _91249) (y : _91249) : (term256 _91249 x y) = (x = y).
Proof. exact (@lem3562355 (x = y)). Qed.
Lemma lem3562357 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term144 _91244 _91249 f x y) (h2 : (f x) = (f y)) : x = y.
Proof. exact (EQ_MP (@lem3562356 _91249 x y) (@lem3562353 _91244 _91249 x f y h1 h2)). Qed.
Lemma lem3562360 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3562362 {_91249 : Type'} (x : _91249) (y : _91249) : (term229 _91249 x y) = (term257 _91249 x y).
Proof. exact (@lem3562360 (x = y)). Qed.
Lemma lem3562365 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) : term257 _91249 x y.
Proof. exact (EQ_MP (@lem3562362 _91249 x y) (@lem3562095 _91249 x y h1)). Qed.
Lemma lem3562368 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (@lem3562365 _91249 x y h1 (@lem3562357 _91244 _91249 x f y h2 h3)). Qed.
Lemma lem3562369 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : term245.
Proof. exact (fun h0 : ~ False => @lem3562368 _91244 _91249 x f y h1 h2 h3). Qed.
Lemma lem3562371 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562372 : term245 = False.
Proof. exact (@lem3562371 False). Qed.
Lemma lem3562373 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562372) (@lem3562369 _91244 _91249 x f y h1 h2 h3)). Qed.
Lemma lem3562387 {_91249 : Type'} (x : _91249) : x = x.
Proof. exact (@lem21386 _91249 x). Qed.
Lemma lem3562388 {_91249 : Type'} (x : _91249) : x = x.
Proof. exact (@lem3562387 _91249 x). Qed.
Lemma lem3562389 {_91249 : Type'} (y : _91249) : y = y.
Proof. exact (@lem3562388 _91249 y). Qed.
Lemma lem3562390 {_91249 : Type'} (y : _91249) : term258 _91249 y.
Proof. exact (fun h0 : term239 _91249 y => @lem3562389 _91249 y). Qed.
Lemma lem3562392 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562393 {_91249 : Type'} (y : _91249) : (term258 _91249 y) = (y = y).
Proof. exact (@lem3562392 (y = y)). Qed.
Lemma lem3562394 {_91249 : Type'} (y : _91249) : y = y.
Proof. exact (EQ_MP (@lem3562393 _91249 y) (@lem3562390 _91249 y)). Qed.
Lemma lem3562397 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3562399 {_91249 : Type'} (y : _91249) : (term239 _91249 y) = (term259 _91249 y).
Proof. exact (@lem3562397 (y = y)). Qed.
Lemma lem3562402 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : term259 _91249 y.
Proof. exact (EQ_MP (@lem3562399 _91249 y) (@lem3562205 _91249 x y h1 h2)). Qed.
Lemma lem3562405 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (@lem3562402 _91249 x y h1 h2 (@lem3562394 _91249 y)). Qed.
Lemma lem3562406 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : term245.
Proof. exact (fun h0 : ~ False => @lem3562405 _91249 x y h1 h2). Qed.
Lemma lem3562408 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562409 : term245 = False.
Proof. exact (@lem3562408 False). Qed.
Lemma lem3562424 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : (f x) = (f y).
Proof. exact (proj1 (@lem3561891 _91244 _91249 x y f h1)). Qed.
Lemma lem3562425 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term242 _91244 _91249 x f y.
Proof. exact (fun h0 : term228 _91244 _91249 x f y => @lem3562424 _91244 _91249 x y f h1). Qed.
Lemma lem3562427 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562428 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) : (term242 _91244 _91249 x f y) = ((f x) = (f y)).
Proof. exact (@lem3562427 ((f x) = (f y))). Qed.
Lemma lem3562429 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : (f x) = (f y).
Proof. exact (EQ_MP (@lem3562428 _91244 _91249 x f y) (@lem3562425 _91244 _91249 x y f h1)). Qed.
Lemma lem3562435 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3562436 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : (term24 _91244 _91249 f _38202 _38203) = (term248 _91244 _91249 _38202 f _38203).
Proof. exact (@lem3562435 (_38202 = _38203) (term228 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562447 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : (term249 _91244 _91249 f _38202 _38203) = (term250 _91244 _91249 _38202 f _38203).
Proof. exact (MK_COMB (@lem3562446) (@lem3562436 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562457 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : (term248 _91244 _91249 _38202 f _38203) = (term248 _91244 _91249 _38202 f _38203).
Proof. exact (eq_refl (term248 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562458 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : ((term24 _91244 _91249 f _38202 _38203) = (term248 _91244 _91249 _38202 f _38203)) = ((term248 _91244 _91249 _38202 f _38203) = (term248 _91244 _91249 _38202 f _38203)).
Proof. exact (MK_COMB (@lem3562447 _91244 _91249 _38202 f _38203) (@lem3562457 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562460 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3562461 (x : Prop) : (x = x) = True.
Proof. exact (@lem3562460 Prop x). Qed.
Lemma lem3562462 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : ((term248 _91244 _91249 _38202 f _38203) = (term248 _91244 _91249 _38202 f _38203)) = True.
Proof. exact (@lem3562461 (term248 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562463 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : ((term24 _91244 _91249 f _38202 _38203) = (term248 _91244 _91249 _38202 f _38203)) = True.
Proof. exact (TRANS (@lem3562458 _91244 _91249 _38202 f _38203) (@lem3562462 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562464 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : True = ((term24 _91244 _91249 f _38202 _38203) = (term248 _91244 _91249 _38202 f _38203)).
Proof. exact (SYM (@lem3562463 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562465 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : (term24 _91244 _91249 f _38202 _38203) = (term248 _91244 _91249 _38202 f _38203).
Proof. exact (EQ_MP (@lem3562464 _91244 _91249 _38202 f _38203) (@lem0)). Qed.
Lemma lem3562466 {_91244 _91249 : Type'} (_38202 : _91249) (_38203 : _91249) (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term248 _91244 _91249 _38202 f _38203.
Proof. exact (EQ_MP (@lem3562465 _91244 _91249 _38202 f _38203) (@lem3562119 _91244 _91249 _38202 _38203 x y f h1)). Qed.
Lemma lem3562468 (b : Prop) (a : Prop) : (a \/ b) = (term251 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3562469 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38202 : _91249) (_38203 : _91249) : (term248 _91244 _91249 _38202 f _38203) = (term252 _91244 _91249 f _38202 _38203).
Proof. exact (@lem3562468 (term228 _91244 _91249 _38202 f _38203) (_38202 = _38203)). Qed.
Lemma lem3562471 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3562472 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : (term253 _91244 _91249 _38202 f _38203) = ((f _38202) = (f _38203)).
Proof. exact (@lem3562471 ((f _38202) = (f _38203))). Qed.
Lemma lem3562473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3562474 {_91244 _91249 : Type'} (_38202 : _91249) (f : _91249 -> _91244) (_38203 : _91249) : (term254 _91244 _91249 _38202 f _38203) = (term255 _91244 _91249 _38202 f _38203).
Proof. exact (MK_COMB (@lem3562473) (@lem3562472 _91244 _91249 _38202 f _38203)). Qed.
Lemma lem3562475 {_91249 : Type'} (_38202 : _91249) (_38203 : _91249) : (_38202 = _38203) = (_38202 = _38203).
Proof. exact (eq_refl (_38202 = _38203)). Qed.
Lemma lem3562476 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38202 : _91249) (_38203 : _91249) : (term252 _91244 _91249 f _38202 _38203) = (term13 _91244 _91249 f _38202 _38203).
Proof. exact (MK_COMB (@lem3562474 _91244 _91249 _38202 f _38203) (@lem3562475 _91249 _38202 _38203)). Qed.
Lemma lem3562477 {_91244 _91249 : Type'} (f : _91249 -> _91244) (_38202 : _91249) (_38203 : _91249) : (term248 _91244 _91249 _38202 f _38203) = (term13 _91244 _91249 f _38202 _38203).
Proof. exact (TRANS (@lem3562469 _91244 _91249 f _38202 _38203) (@lem3562476 _91244 _91249 f _38202 _38203)). Qed.
Lemma lem3562480 {_91244 _91249 : Type'} (_38202 : _91249) (_38203 : _91249) (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term13 _91244 _91249 f _38202 _38203.
Proof. exact (EQ_MP (@lem3562477 _91244 _91249 f _38202 _38203) (@lem3562466 _91244 _91249 _38202 _38203 x y f h1)). Qed.
Lemma lem3562481 {_91244 _91249 : Type'} (_38202 : _91249) (_38203 : _91249) (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term13 _91244 _91249 f _38202 _38203.
Proof. exact (@lem3562480 _91244 _91249 _38202 _38203 x y f h1). Qed.
Lemma lem3562482 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term13 _91244 _91249 f x y.
Proof. exact (@lem3562481 _91244 _91249 x y x y f h1). Qed.
Lemma lem3562485 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : x = y.
Proof. exact (@lem3562482 _91244 _91249 x y f h1 (@lem3562429 _91244 _91249 x y f h1)). Qed.
Lemma lem3562486 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term256 _91249 x y.
Proof. exact (fun h0 : term229 _91249 x y => @lem3562485 _91244 _91249 x y f h1). Qed.
Lemma lem3562488 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562489 {_91249 : Type'} (x : _91249) (y : _91249) : (term256 _91249 x y) = (x = y).
Proof. exact (@lem3562488 (x = y)). Qed.
Lemma lem3562490 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : x = y.
Proof. exact (EQ_MP (@lem3562489 _91249 x y) (@lem3562486 _91244 _91249 x y f h1)). Qed.
Lemma lem3562493 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3562495 {_91249 : Type'} (x : _91249) (y : _91249) : (term229 _91249 x y) = (term257 _91249 x y).
Proof. exact (@lem3562493 (x = y)). Qed.
Lemma lem3562498 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term257 _91249 x y.
Proof. exact (EQ_MP (@lem3562495 _91249 x y) (@lem3562123 _91244 _91249 x y f h1)). Qed.
Lemma lem3562501 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : False.
Proof. exact (@lem3562498 _91244 _91249 x y f h1 (@lem3562490 _91244 _91249 x y f h1)). Qed.
Lemma lem3562502 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : term245.
Proof. exact (fun h0 : ~ False => @lem3562501 _91244 _91249 x y f h1). Qed.
Lemma lem3562504 (p : Prop) : (term243 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3562505 : term245 = False.
Proof. exact (@lem3562504 False). Qed.
Lemma lem3562506 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term179 _91244 _91249 x y f) : False.
Proof. exact (EQ_MP (@lem3562505) (@lem3562502 _91244 _91249 x y f h1)). Qed.
Lemma lem3562507 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562409) (@lem3562406 _91249 x y h1 h2)). Qed.
Lemma lem3562508 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562276) (@lem3562273 _91244 _91249 f x y h1 h2)). Qed.
Lemma lem3562509 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3562507 _91249 x y h1 h2) (fun h3 : False => @lem3562107 _91249 x y h2)). Qed.
Lemma lem3562510 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562509 _91249 x y h1 h2) (@lem3562107 _91249 x y h2)). Qed.
Lemma lem3562511 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : (term229 _91249 x y) = False.
Proof. exact (prop_ext (fun h3 : term229 _91249 x y => @lem3562510 _91249 x y h1 h2) (fun h3 : False => @lem3562105 _91249 x y h1)). Qed.
Lemma lem3562512 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562511 _91249 x y h1 h2) (@lem3562105 _91249 x y h1)). Qed.
Lemma lem3562513 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (f y) => @lem3562373 _91244 _91249 x f y h1 h2 h3) (fun h4 : False => @lem3562097 _91244 _91249 x f y h3)). Qed.
Lemma lem3562514 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562513 _91244 _91249 x f y h1 h2 h3) (@lem3562097 _91244 _91249 x f y h3)). Qed.
Lemma lem3562515 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : (term229 _91249 x y) = False.
Proof. exact (prop_ext (fun h4 : term229 _91249 x y => @lem3562514 _91244 _91249 x f y h1 h2 h3) (fun h4 : False => @lem3562095 _91249 x y h1)). Qed.
Lemma lem3562516 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562515 _91244 _91249 x f y h1 h2 h3) (@lem3562095 _91249 x y h1)). Qed.
Lemma lem3562517 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3562508 _91244 _91249 f x y h1 h2) (fun h3 : False => @lem3562087 _91249 x y h2)). Qed.
Lemma lem3562518 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562517 _91244 _91249 f x y h1 h2) (@lem3562087 _91249 x y h2)). Qed.
Lemma lem3562519 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : (term228 _91244 _91249 x f y) = False.
Proof. exact (prop_ext (fun h3 : term228 _91244 _91249 x f y => @lem3562518 _91244 _91249 f x y h1 h2) (fun h3 : False => @lem3562085 _91244 _91249 x f y h1)). Qed.
Lemma lem3562520 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562519 _91244 _91249 f x y h1 h2) (@lem3562085 _91244 _91249 x f y h1)). Qed.
Lemma lem3562521 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (f y) => @lem3562240 _91244 _91249 x f y h1 h2) (fun h3 : False => @lem3562077 _91244 _91249 x f y h2)). Qed.
Lemma lem3562522 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562521 _91244 _91249 x f y h1 h2) (@lem3562077 _91244 _91249 x f y h2)). Qed.
Lemma lem3562523 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : (term228 _91244 _91249 x f y) = False.
Proof. exact (prop_ext (fun h3 : term228 _91244 _91249 x f y => @lem3562522 _91244 _91249 x f y h1 h2) (fun h3 : False => @lem3562075 _91244 _91249 x f y h1)). Qed.
Lemma lem3562524 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562523 _91244 _91249 x f y h1 h2) (@lem3562075 _91244 _91249 x f y h1)). Qed.
Lemma lem3562525 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3562512 _91249 x y h1 h2) (fun h3 : False => @lem3561991 _91249 x y h2)). Qed.
Lemma lem3562526 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562525 _91249 x y h1 h2) (@lem3561991 _91249 x y h2)). Qed.
Lemma lem3562527 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : (term229 _91249 x y) = False.
Proof. exact (prop_ext (fun h3 : term229 _91249 x y => @lem3562526 _91249 x y h1 h2) (fun h3 : False => @lem3561987 _91249 x y h1)). Qed.
Lemma lem3562528 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562527 _91249 x y h1 h2) (@lem3561987 _91249 x y h1)). Qed.
Lemma lem3562529 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (f y) => @lem3562516 _91244 _91249 x f y h1 h2 h3) (fun h4 : False => @lem3561967 _91244 _91249 x f y h3)). Qed.
Lemma lem3562530 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562529 _91244 _91249 x f y h1 h2 h3) (@lem3561967 _91244 _91249 x f y h3)). Qed.
Lemma lem3562531 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : (term229 _91249 x y) = False.
Proof. exact (prop_ext (fun h4 : term229 _91249 x y => @lem3562530 _91244 _91249 x f y h1 h2 h3) (fun h4 : False => @lem3561963 _91249 x y h1)). Qed.
Lemma lem3562532 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562531 _91244 _91249 x f y h1 h2 h3) (@lem3561963 _91249 x y h1)). Qed.
Lemma lem3562533 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3562520 _91244 _91249 f x y h1 h2) (fun h3 : False => @lem3561943 _91249 x y h2)). Qed.
Lemma lem3562534 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562533 _91244 _91249 f x y h1 h2) (@lem3561943 _91249 x y h2)). Qed.
Lemma lem3562535 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : (term228 _91244 _91249 x f y) = False.
Proof. exact (prop_ext (fun h3 : term228 _91244 _91249 x f y => @lem3562534 _91244 _91249 f x y h1 h2) (fun h3 : False => @lem3561939 _91244 _91249 x f y h1)). Qed.
Lemma lem3562536 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562535 _91244 _91249 f x y h1 h2) (@lem3561939 _91244 _91249 x f y h1)). Qed.
Lemma lem3562537 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (f y) => @lem3562524 _91244 _91249 x f y h1 h2) (fun h3 : False => @lem3561919 _91244 _91249 x f y h2)). Qed.
Lemma lem3562538 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562537 _91244 _91249 x f y h1 h2) (@lem3561919 _91244 _91249 x f y h2)). Qed.
Lemma lem3562539 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : (term228 _91244 _91249 x f y) = False.
Proof. exact (prop_ext (fun h3 : term228 _91244 _91249 x f y => @lem3562538 _91244 _91249 x f y h1 h2) (fun h3 : False => @lem3561915 _91244 _91249 x f y h1)). Qed.
Lemma lem3562540 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562539 _91244 _91249 x f y h1 h2) (@lem3561915 _91244 _91249 x f y h1)). Qed.
Lemma lem3562541 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3562528 _91249 x y h1 h2) (fun h3 : False => @lem3561991 _91249 x y h2)). Qed.
Lemma lem3562542 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562541 _91249 x y h1 h2) (@lem3561991 _91249 x y h2)). Qed.
Lemma lem3562543 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : (term229 _91249 x y) = False.
Proof. exact (prop_ext (fun h3 : term229 _91249 x y => @lem3562542 _91249 x y h1 h2) (fun h3 : False => @lem3561987 _91249 x y h1)). Qed.
Lemma lem3562544 {_91249 : Type'} (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562543 _91249 x y h1 h2) (@lem3561987 _91249 x y h1)). Qed.
Lemma lem3562545 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (f y) => @lem3562532 _91244 _91249 x f y h1 h2 h3) (fun h4 : False => @lem3561967 _91244 _91249 x f y h3)). Qed.
Lemma lem3562546 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562545 _91244 _91249 x f y h1 h2 h3) (@lem3561967 _91244 _91249 x f y h3)). Qed.
Lemma lem3562547 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : (term229 _91249 x y) = False.
Proof. exact (prop_ext (fun h4 : term229 _91249 x y => @lem3562546 _91244 _91249 x f y h1 h2 h3) (fun h4 : False => @lem3561963 _91249 x y h1)). Qed.
Lemma lem3562548 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) (h3 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562547 _91244 _91249 x f y h1 h2 h3) (@lem3561963 _91249 x y h1)). Qed.
Lemma lem3562549 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem3562536 _91244 _91249 f x y h1 h2) (fun h3 : False => @lem3561943 _91249 x y h2)). Qed.
Lemma lem3562550 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562549 _91244 _91249 f x y h1 h2) (@lem3561943 _91249 x y h2)). Qed.
Lemma lem3562551 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : (term228 _91244 _91249 x f y) = False.
Proof. exact (prop_ext (fun h3 : term228 _91244 _91249 x f y => @lem3562550 _91244 _91249 f x y h1 h2) (fun h3 : False => @lem3561939 _91244 _91249 x f y h1)). Qed.
Lemma lem3562552 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem3562551 _91244 _91249 f x y h1 h2) (@lem3561939 _91244 _91249 x f y h1)). Qed.
Lemma lem3562553 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : ((f x) = (f y)) = False.
Proof. exact (prop_ext (fun h3 : (f x) = (f y) => @lem3562540 _91244 _91249 x f y h1 h2) (fun h3 : False => @lem3561919 _91244 _91249 x f y h2)). Qed.
Lemma lem3562554 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562553 _91244 _91249 x f y h1 h2) (@lem3561919 _91244 _91249 x f y h2)). Qed.
Lemma lem3562555 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : (term228 _91244 _91249 x f y) = False.
Proof. exact (prop_ext (fun h3 : term228 _91244 _91249 x f y => @lem3562554 _91244 _91249 x f y h1 h2) (fun h3 : False => @lem3561915 _91244 _91249 x f y h1)). Qed.
Lemma lem3562556 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : (f x) = (f y)) : False.
Proof. exact (EQ_MP (@lem3562555 _91244 _91249 x f y h1 h2) (@lem3561915 _91244 _91249 x f y h1)). Qed.
Lemma lem3562557 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term229 _91249 x y) (h2 : term144 _91244 _91249 f x y) : False.
Proof. exact (or_elim (@lem3561883 _91244 _91249 f x y h2) (fun h0 : (f x) = (f y) => @lem3562548 _91244 _91249 x f y h1 h2 h0) (fun h0 : x = y => @lem3562544 _91249 x y h1 h0)). Qed.
Lemma lem3562558 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term228 _91244 _91249 x f y) (h2 : term144 _91244 _91249 f x y) : False.
Proof. exact (or_elim (@lem3561883 _91244 _91249 f x y h2) (fun h0 : (f x) = (f y) => @lem3562556 _91244 _91249 x f y h1 h0) (fun h0 : x = y => @lem3562552 _91244 _91249 f x y h1 h0)). Qed.
Lemma lem3562559 {_91244 _91249 : Type'} (f : _91249 -> _91244) (x : _91249) (y : _91249) (h1 : term144 _91244 _91249 f x y) : False.
Proof. exact (or_elim (@lem3561882 _91244 _91249 f x y h1) (fun h0 : term228 _91244 _91249 x f y => @lem3562558 _91244 _91249 f x y h0 h1) (fun h0 : term229 _91249 x y => @lem3562557 _91244 _91249 f x y h0 h1)). Qed.
Lemma lem3562560 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term220 _91244 _91249 x y f) : False.
Proof. exact (or_elim (@lem3561877 _91244 _91249 x y f h1) (fun h0 : term144 _91244 _91249 f x y => @lem3562559 _91244 _91249 f x y h0) (fun h0 : term179 _91244 _91249 x y f => @lem3562506 _91244 _91249 x y f h0)). Qed.
Lemma lem3562561 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term220 _91244 _91249 x y f) : (term220 _91244 _91249 x y f) = False.
Proof. exact (prop_ext (fun h2 : term220 _91244 _91249 x y f => @lem3562560 _91244 _91249 x y f h1) (fun h2 : False => @lem3561877 _91244 _91249 x y f h1)). Qed.
Lemma lem3562562 {_91244 _91249 : Type'} (x : _91249) (y : _91249) (f : _91249 -> _91244) (h1 : term220 _91244 _91249 x y f) : False.
Proof. exact (EQ_MP (@lem3562561 _91244 _91249 x y f h1) (@lem3561877 _91244 _91249 x y f h1)). Qed.
Lemma lem3562563 {_91244 _91249 : Type'} (x : _91249) (f : _91249 -> _91244) (h1 : term223 _91244 _91249 x f) : False.
Proof. exact (ex_elim (@lem3561728 _91244 _91249 x f h1) (fun y : _91249 => fun h0 : term222 _91244 _91249 x f y => @lem3562562 _91244 _91249 x y f h0)). Qed.
Lemma lem3562564 {_91244 _91249 : Type'} (f : _91249 -> _91244) (h1 : term21 _91244 _91249 f) : False.
Proof. exact (ex_elim (@lem3561727 _91244 _91249 f h1) (fun x : _91249 => fun h0 : term224 _91244 _91249 f x => @lem3562563 _91244 _91249 x f h0)). Qed.
Lemma lem3562565 {_91244 _91249 : Type'} (f : _91249 -> _91244) (h1 : term21 _91244 _91249 f) : (term21 _91244 _91249 f) = False.
Proof. exact (prop_ext (fun h2 : term21 _91244 _91249 f => @lem3562564 _91244 _91249 f h1) (fun h2 : False => @lem3561041 _91244 _91249 f h1)). Qed.
Lemma lem3562566 {_91244 _91249 : Type'} (f : _91249 -> _91244) (h1 : term21 _91244 _91249 f) : False.
Proof. exact (EQ_MP (@lem3562565 _91244 _91249 f h1) (@lem3561041 _91244 _91249 f h1)). Qed.
Lemma lem3562567 {_91244 _91249 : Type'} (f : _91249 -> _91244) : term20 _91244 _91249 f.
Proof. exact (fun h0 : term21 _91244 _91249 f => @lem3562566 _91244 _91249 f h0). Qed.
Lemma lem3562568 {_91244 _91249 : Type'} (f : _91249 -> _91244) : (term17 _91244 _91249 f) = (term12 _91244 _91249 f).
Proof. exact (EQ_MP (@lem3561040 _91244 _91249 f) (@lem3562567 _91244 _91249 f)). Qed.
Lemma lem3562573 {_91244 _91249 : Type'} : term1 _91244 _91249.
Proof. exact (fun f : _91249 -> _91244 => @lem3562568 _91244 _91249 f). Qed.
Lemma lem3562574 {_91244 _91249 : Type'} : term2 _91244 _91249.
Proof. exact (EQ_MP (@lem3561036 _91244 _91249) (@lem3562573 _91244 _91249)). Qed.
Lemma lem3562576 {_91244 _91249 : Type'} : term2 _91244 _91249.
Proof. exact (@lem3560939 _91244 _91249 (@lem3562574 _91244 _91249)). Qed.
Lemma lem3562577 {_91244 _91249 : Type'} (h1 : term3 _91244 _91249) : False.
Proof. exact (@lem3562576 _91244 _91249 (@lem3560923 _91244 _91249 h1)). Qed.
Lemma lem3562578 {_91244 _91249 : Type'} (h1 : term3 _91244 _91249) : (term3 _91244 _91249) = False.
Proof. exact (prop_ext (fun h2 : term3 _91244 _91249 => @lem3562577 _91244 _91249 h1) (fun h2 : False => @lem3560923 _91244 _91249 h1)). Qed.
Lemma lem3562579 {_91244 _91249 : Type'} (h1 : term3 _91244 _91249) : False.
Proof. exact (EQ_MP (@lem3562578 _91244 _91249 h1) (@lem3560923 _91244 _91249 h1)). Qed.
Lemma lem3562580 {_91244 _91249 : Type'} : term2 _91244 _91249.
Proof. exact (fun h0 : term3 _91244 _91249 => @lem3562579 _91244 _91249 h0). Qed.
Lemma lem3562581 {_91244 _91249 : Type'} : term1 _91244 _91249.
Proof. exact (EQ_MP (@lem3560922 _91244 _91249) (@lem3562580 _91244 _91249)). Qed.
