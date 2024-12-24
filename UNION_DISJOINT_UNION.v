Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_DISJOINT_UNION_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_UNION_spec.
Require Import PAIR_EQ_spec.
Require Import disjoint_union_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm69_spec.
Lemma lem4482971 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4482972 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4482973 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4482972 t1) (@lem4482971 t1)). Qed.
Lemma lem4482974 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4482973 t1 t2). Qed.
Lemma lem4482975 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4482976 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4482975 t1 t2) (@lem4482974 t1 t2)). Qed.
Lemma lem4482977 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4482976 t1 t2 t3). Qed.
Lemma lem4482978 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4482979 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4482978 t1 t2 t3) (@lem4482977 t1 t2 t3)). Qed.
Lemma lem4482980 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4482979 t1 t2 t3)). Qed.
Lemma lem4483012 {_83064 : Type'} : term7 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem4483013 {_83064 : Type'} (P : type919 _83064) : term8 _83064 P.
Proof. exact (@lem4483012 _83064 P). Qed.
Lemma lem4483014 {_83064 : Type'} (P : type919 _83064) : (term8 _83064 P) = (term9 _83064 P).
Proof. exact (eq_refl (term8 _83064 P)). Qed.
Lemma lem4483015 {_83064 : Type'} (P : type919 _83064) : term9 _83064 P.
Proof. exact (EQ_MP (@lem4483014 _83064 P) (@lem4483013 _83064 P)). Qed.
Lemma lem4483016 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term10 _83064 P x.
Proof. exact (@lem4483015 _83064 P x). Qed.
Lemma lem4483017 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term10 _83064 P x) = ((term11 _83064 x P) = (term12 _83064 P x)).
Proof. exact (eq_refl (term10 _83064 P x)). Qed.
Lemma lem4483019 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem4483020 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4483021 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem4483020 A s) (@lem4483019 A s)). Qed.
Lemma lem4483022 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem4483021 A s t). Qed.
Lemma lem4483023 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = (term16 A s t).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem4483024 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (EQ_MP (@lem4483023 A s t) (@lem4483022 A s t)). Qed.
Lemma lem4483025 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term17 A s t x.
Proof. exact (@lem4483024 A s t x). Qed.
Lemma lem4483026 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A s t x) = ((term18 A x s t) = (term19 A s x t)).
Proof. exact (eq_refl (term17 A s t x)). Qed.
Lemma lem4483028 {A K : Type'} (k : K -> Prop) : term20 A K k.
Proof. exact (@lem4464464 A K k). Qed.
Lemma lem4483029 {A K : Type'} (k : K -> Prop) : (term20 A K k) = (term21 A K k).
Proof. exact (eq_refl (term20 A K k)). Qed.
Lemma lem4483030 {A K : Type'} (k : K -> Prop) : term21 A K k.
Proof. exact (EQ_MP (@lem4483029 A K k) (@lem4483028 A K k)). Qed.
Lemma lem4483031 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term22 A K k s.
Proof. exact (@lem4483030 A K k s). Qed.
Lemma lem4483032 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = ((@disjoint_union A K k s) = (term23 A K k s)).
Proof. exact (eq_refl (term22 A K k s)). Qed.
Lemma lem4483034 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4483035 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4483036 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem4483035 A s) (@lem4483034 A s)). Qed.
Lemma lem4483037 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem4483036 A s t). Qed.
Lemma lem4483038 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem4483043 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4483038 A s t) (@lem4483037 A s t)). Qed.
Lemma lem4483044 {A K : Type'} (s : type1223 A K) (t : type1223 A K) : (s = t) = (term28 A K s t).
Proof. exact (@lem4483043 (prod K A) s t). Qed.
Lemma lem4483045 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term29 A K s k t) = (term30 A K k s t)) = (term31 A K k s t).
Proof. exact (@lem4483044 A K (term29 A K s k t) (term30 A K k s t)). Qed.
Lemma lem4483055 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term18 A x s t) = (term19 A s x t).
Proof. exact (EQ_MP (@lem4483026 A s x t) (@lem4483025 A s t x)). Qed.
Lemma lem4483056 {A K : Type'} (s : type1223 A K) (x : prod K A) (t : type1223 A K) : (term32 A K x s t) = (term33 A K s x t).
Proof. exact (@lem4483055 (prod K A) s x t). Qed.
Lemma lem4483057 {A K : Type'} (s : type1470 A K) (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term34 A K x s k t) = (term35 A K s x k t).
Proof. exact (@lem4483056 A K (@disjoint_union A K k s) x (@disjoint_union A K k t)). Qed.
Lemma lem4483061 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4483032 A K k s) (@lem4483031 A K k s)). Qed.
Lemma lem4483062 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4483061 A K k s). Qed.
Lemma lem4483073 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4483074 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term36 A K x k s) = (term37 A K x k s).
Proof. exact (MK_COMB (@lem4483073 A K x) (@lem4483062 A K k s)). Qed.
Lemma lem4483076 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem4483017 _83064 P x) (@lem4483016 _83064 P x)). Qed.
Lemma lem4483077 {A K : Type'} (P : type916 A K) (x : prod K A) : (term38 A K x P) = (term39 A K P x).
Proof. exact (@lem4483076 (prod K A) P x). Qed.
Lemma lem4483078 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term40 A K x k s) = (term41 A K k s x).
Proof. exact (@lem4483077 A K (term42 A K k s) x). Qed.
Lemma lem4483079 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term43 A K k s GEN_PVAR_143) = (term44 A K GEN_PVAR_143 k s).
Proof. exact (eq_refl (term43 A K k s GEN_PVAR_143)). Qed.
Lemma lem4483080 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term45 A K k s) = (term46 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4483079 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4483081 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4483082 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term47 A K k s) = (term23 A K k s).
Proof. exact (MK_COMB (@lem4483081 A K) (@lem4483080 A K k s)). Qed.
Lemma lem4483083 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4483084 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term40 A K x k s) = (term37 A K x k s).
Proof. exact (MK_COMB (@lem4483083 A K x) (@lem4483082 A K k s)). Qed.
Lemma lem4483085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483086 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term48 A K x k s) = (term49 A K x k s).
Proof. exact (MK_COMB (@lem4483085) (@lem4483084 A K x k s)). Qed.
Lemma lem4483087 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term41 A K k s x) = (term50 A K x k s).
Proof. exact (eq_refl (term41 A K k s x)). Qed.
Lemma lem4483088 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : ((term40 A K x k s) = (term41 A K k s x)) = ((term37 A K x k s) = (term50 A K x k s)).
Proof. exact (MK_COMB (@lem4483086 A K x k s) (@lem4483087 A K x k s)). Qed.
Lemma lem4483089 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term37 A K x k s) = (term50 A K x k s).
Proof. exact (EQ_MP (@lem4483088 A K x k s) (@lem4483078 A K k s x)). Qed.
Lemma lem4483099 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4483100 {A K : Type'} (f : type1534 A K) (y : Prop) : (term52 A K f y) = (f y).
Proof. exact (@lem4483099 Prop (type1223 A K) f y). Qed.
Lemma lem4483101 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (s : type1470 A K) (i : K) : (term53 A K x k x' s i) = (term54 A K x k x' s i).
Proof. exact (@lem4483100 A K (term55 A K x) (term56 A K k x' s i)). Qed.
Lemma lem4483102 {A K : Type'} (p : Prop) (x : prod K A) : (term57 A K x p) = (term58 A K p x).
Proof. exact (eq_refl (term57 A K x p)). Qed.
Lemma lem4483103 {A K : Type'} (x : prod K A) : (term59 A K x) = (term55 A K x).
Proof. exact (fun_ext (fun p : Prop => @lem4483102 A K p x)). Qed.
Lemma lem4483104 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term56 A K k x s i) = (term56 A K k x s i).
Proof. exact (eq_refl (term56 A K k x s i)). Qed.
Lemma lem4483105 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (s : type1470 A K) (i : K) : (term53 A K x k x' s i) = (term54 A K x k x' s i).
Proof. exact (MK_COMB (@lem4483103 A K x) (@lem4483104 A K k x' s i)). Qed.
Lemma lem4483106 {A K : Type'} : (@eq ((prod K A) -> Prop)) = (@eq ((prod K A) -> Prop)).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop))). Qed.
Lemma lem4483107 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (s : type1470 A K) (i : K) : (term60 A K x k x' s i) = (term61 A K x k x' s i).
Proof. exact (MK_COMB (@lem4483106 A K) (@lem4483105 A K x k x' s i)). Qed.
Lemma lem4483108 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x s i) = (term62 A K k x s i x').
Proof. exact (eq_refl (term54 A K x' k x s i)). Qed.
Lemma lem4483109 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : ((term53 A K x' k x s i) = (term54 A K x' k x s i)) = ((term54 A K x' k x s i) = (term62 A K k x s i x')).
Proof. exact (MK_COMB (@lem4483107 A K x' k x s i) (@lem4483108 A K k x s i x')). Qed.
Lemma lem4483110 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x s i) = (term62 A K k x s i x').
Proof. exact (EQ_MP (@lem4483109 A K k x s i x') (@lem4483101 A K x' k x s i)). Qed.
Lemma lem4483119 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4483120 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k s i x') = (term64 A K k s x i x').
Proof. exact (MK_COMB (@lem4483110 A K k x' s i x) (@lem4483119 A K i x')). Qed.
Lemma lem4483122 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4483123 {A K : Type'} (f : type1223 A K) (y : prod K A) : (term65 A K f y) = (f y).
Proof. exact (@lem4483122 (prod K A) Prop f y). Qed.
Lemma lem4483124 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k s x i x') = (term64 A K k s x i x').
Proof. exact (@lem4483123 A K (term62 A K k x' s i x) (@pair K A i x')). Qed.
Lemma lem4483125 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) (t : prod K A) : (term67 A K k x s i x' t) = (term68 A K k x s i x' t).
Proof. exact (eq_refl (term67 A K k x s i x' t)). Qed.
Lemma lem4483126 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : (term69 A K k x s i x') = (term62 A K k x s i x').
Proof. exact (fun_ext (fun t : prod K A => @lem4483125 A K k x s i x' t)). Qed.
Lemma lem4483127 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4483128 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k s x i x') = (term64 A K k s x i x').
Proof. exact (MK_COMB (@lem4483126 A K k x' s i x) (@lem4483127 A K i x')). Qed.
Lemma lem4483129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483130 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term70 A K k s x i x') = (term71 A K k s x i x').
Proof. exact (MK_COMB (@lem4483129) (@lem4483128 A K k s x i x')). Qed.
Lemma lem4483131 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term64 A K k s x i x')). Qed.
Lemma lem4483132 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term66 A K k s x i x') = (term64 A K k s x i x')) = ((term64 A K k s x i x') = (term72 A K k s x i x')).
Proof. exact (MK_COMB (@lem4483130 A K k s x i x') (@lem4483131 A K k s x i x')). Qed.
Lemma lem4483133 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (EQ_MP (@lem4483132 A K k s x i x') (@lem4483124 A K k s x i x')). Qed.
Lemma lem4483142 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k s i x') = (term72 A K k s x i x').
Proof. exact (TRANS (@lem4483120 A K k s x i x') (@lem4483133 A K k s x i x')). Qed.
Lemma lem4483143 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term73 A K x k s i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4483142 A K k s x i x')). Qed.
Lemma lem4483144 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4483145 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term75 A K x k s i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4483144 A) (@lem4483143 A K k s x i)). Qed.
Lemma lem4483150 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term77 A K x k s) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4483145 A K k s x i)). Qed.
Lemma lem4483151 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4483152 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term50 A K x k s) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4483151 K) (@lem4483150 A K k s x)). Qed.
Lemma lem4483157 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term37 A K x k s) = (term79 A K k s x).
Proof. exact (TRANS (@lem4483089 A K x k s) (@lem4483152 A K k s x)). Qed.
Lemma lem4483158 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term36 A K x k s) = (term79 A K k s x).
Proof. exact (TRANS (@lem4483074 A K x k s) (@lem4483157 A K k s x)). Qed.
Lemma lem4483159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4483160 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term80 A K x k s) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4483159) (@lem4483158 A K k s x)). Qed.
Lemma lem4483162 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4483032 A K k s) (@lem4483031 A K k s)). Qed.
Lemma lem4483163 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4483162 A K k s). Qed.
Lemma lem4483164 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (term23 A K k t).
Proof. exact (@lem4483163 A K k t). Qed.
Lemma lem4483175 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4483176 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term36 A K x k t) = (term37 A K x k t).
Proof. exact (MK_COMB (@lem4483175 A K x) (@lem4483164 A K k t)). Qed.
Lemma lem4483178 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem4483017 _83064 P x) (@lem4483016 _83064 P x)). Qed.
Lemma lem4483179 {A K : Type'} (P : type916 A K) (x : prod K A) : (term38 A K x P) = (term39 A K P x).
Proof. exact (@lem4483178 (prod K A) P x). Qed.
Lemma lem4483180 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term40 A K x k t) = (term41 A K k t x).
Proof. exact (@lem4483179 A K (term42 A K k t) x). Qed.
Lemma lem4483181 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (t : type1470 A K) : (term43 A K k t GEN_PVAR_143) = (term44 A K GEN_PVAR_143 k t).
Proof. exact (eq_refl (term43 A K k t GEN_PVAR_143)). Qed.
Lemma lem4483182 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term45 A K k t) = (term46 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4483181 A K GEN_PVAR_143 k t)). Qed.
Lemma lem4483183 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4483184 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term47 A K k t) = (term23 A K k t).
Proof. exact (MK_COMB (@lem4483183 A K) (@lem4483182 A K k t)). Qed.
Lemma lem4483185 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4483186 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term40 A K x k t) = (term37 A K x k t).
Proof. exact (MK_COMB (@lem4483185 A K x) (@lem4483184 A K k t)). Qed.
Lemma lem4483187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483188 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term48 A K x k t) = (term49 A K x k t).
Proof. exact (MK_COMB (@lem4483187) (@lem4483186 A K x k t)). Qed.
Lemma lem4483189 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term41 A K k t x) = (term50 A K x k t).
Proof. exact (eq_refl (term41 A K k t x)). Qed.
Lemma lem4483190 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : ((term40 A K x k t) = (term41 A K k t x)) = ((term37 A K x k t) = (term50 A K x k t)).
Proof. exact (MK_COMB (@lem4483188 A K x k t) (@lem4483189 A K x k t)). Qed.
Lemma lem4483191 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term37 A K x k t) = (term50 A K x k t).
Proof. exact (EQ_MP (@lem4483190 A K x k t) (@lem4483180 A K k t x)). Qed.
Lemma lem4483201 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4483202 {A K : Type'} (f : type1534 A K) (y : Prop) : (term52 A K f y) = (f y).
Proof. exact (@lem4483201 Prop (type1223 A K) f y). Qed.
Lemma lem4483203 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (t : type1470 A K) (i : K) : (term53 A K x k x' t i) = (term54 A K x k x' t i).
Proof. exact (@lem4483202 A K (term55 A K x) (term56 A K k x' t i)). Qed.
Lemma lem4483204 {A K : Type'} (p : Prop) (x : prod K A) : (term57 A K x p) = (term58 A K p x).
Proof. exact (eq_refl (term57 A K x p)). Qed.
Lemma lem4483205 {A K : Type'} (x : prod K A) : (term59 A K x) = (term55 A K x).
Proof. exact (fun_ext (fun p : Prop => @lem4483204 A K p x)). Qed.
Lemma lem4483206 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term56 A K k x t i) = (term56 A K k x t i).
Proof. exact (eq_refl (term56 A K k x t i)). Qed.
Lemma lem4483207 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (t : type1470 A K) (i : K) : (term53 A K x k x' t i) = (term54 A K x k x' t i).
Proof. exact (MK_COMB (@lem4483205 A K x) (@lem4483206 A K k x' t i)). Qed.
Lemma lem4483208 {A K : Type'} : (@eq ((prod K A) -> Prop)) = (@eq ((prod K A) -> Prop)).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop))). Qed.
Lemma lem4483209 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (t : type1470 A K) (i : K) : (term60 A K x k x' t i) = (term61 A K x k x' t i).
Proof. exact (MK_COMB (@lem4483208 A K) (@lem4483207 A K x k x' t i)). Qed.
Lemma lem4483210 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x t i) = (term62 A K k x t i x').
Proof. exact (eq_refl (term54 A K x' k x t i)). Qed.
Lemma lem4483211 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : ((term53 A K x' k x t i) = (term54 A K x' k x t i)) = ((term54 A K x' k x t i) = (term62 A K k x t i x')).
Proof. exact (MK_COMB (@lem4483209 A K x' k x t i) (@lem4483210 A K k x t i x')). Qed.
Lemma lem4483212 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x t i) = (term62 A K k x t i x').
Proof. exact (EQ_MP (@lem4483211 A K k x t i x') (@lem4483203 A K x' k x t i)). Qed.
Lemma lem4483221 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4483222 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k t i x') = (term64 A K k t x i x').
Proof. exact (MK_COMB (@lem4483212 A K k x' t i x) (@lem4483221 A K i x')). Qed.
Lemma lem4483224 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4483225 {A K : Type'} (f : type1223 A K) (y : prod K A) : (term65 A K f y) = (f y).
Proof. exact (@lem4483224 (prod K A) Prop f y). Qed.
Lemma lem4483226 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k t x i x') = (term64 A K k t x i x').
Proof. exact (@lem4483225 A K (term62 A K k x' t i x) (@pair K A i x')). Qed.
Lemma lem4483227 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) (t' : prod K A) : (term67 A K k x t i x' t') = (term68 A K k x t i x' t').
Proof. exact (eq_refl (term67 A K k x t i x' t')). Qed.
Lemma lem4483228 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term69 A K k x t i x') = (term62 A K k x t i x').
Proof. exact (fun_ext (fun t' : prod K A => @lem4483227 A K k x t i x' t')). Qed.
Lemma lem4483229 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4483230 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k t x i x') = (term64 A K k t x i x').
Proof. exact (MK_COMB (@lem4483228 A K k x' t i x) (@lem4483229 A K i x')). Qed.
Lemma lem4483231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483232 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term70 A K k t x i x') = (term71 A K k t x i x').
Proof. exact (MK_COMB (@lem4483231) (@lem4483230 A K k t x i x')). Qed.
Lemma lem4483233 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term64 A K k t x i x')). Qed.
Lemma lem4483234 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term66 A K k t x i x') = (term64 A K k t x i x')) = ((term64 A K k t x i x') = (term72 A K k t x i x')).
Proof. exact (MK_COMB (@lem4483232 A K k t x i x') (@lem4483233 A K k t x i x')). Qed.
Lemma lem4483235 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (EQ_MP (@lem4483234 A K k t x i x') (@lem4483226 A K k t x i x')). Qed.
Lemma lem4483244 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k t i x') = (term72 A K k t x i x').
Proof. exact (TRANS (@lem4483222 A K k t x i x') (@lem4483235 A K k t x i x')). Qed.
Lemma lem4483245 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term73 A K x k t i) = (term74 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4483244 A K k t x i x')). Qed.
Lemma lem4483246 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4483247 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term75 A K x k t i) = (term76 A K k t x i).
Proof. exact (MK_COMB (@lem4483246 A) (@lem4483245 A K k t x i)). Qed.
Lemma lem4483252 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term77 A K x k t) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4483247 A K k t x i)). Qed.
Lemma lem4483253 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4483254 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term50 A K x k t) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4483253 K) (@lem4483252 A K k t x)). Qed.
Lemma lem4483259 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term37 A K x k t) = (term79 A K k t x).
Proof. exact (TRANS (@lem4483191 A K x k t) (@lem4483254 A K k t x)). Qed.
Lemma lem4483260 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term36 A K x k t) = (term79 A K k t x).
Proof. exact (TRANS (@lem4483176 A K x k t) (@lem4483259 A K k t x)). Qed.
Lemma lem4483261 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term35 A K s x k t) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4483160 A K k s x) (@lem4483260 A K k t x)). Qed.
Lemma lem4483264 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term34 A K x s k t) = (term82 A K s k t x).
Proof. exact (TRANS (@lem4483057 A K s x k t) (@lem4483261 A K s k t x)). Qed.
Lemma lem4483265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483266 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term83 A K x s k t) = (term84 A K s k t x).
Proof. exact (MK_COMB (@lem4483265) (@lem4483264 A K s k t x)). Qed.
Lemma lem4483268 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4483032 A K k s) (@lem4483031 A K k s)). Qed.
Lemma lem4483269 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4483268 A K k s). Qed.
Lemma lem4483270 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term30 A K k s t) = (term85 A K k s t).
Proof. exact (@lem4483269 A K k (term86 A K s t)). Qed.
Lemma lem4483282 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4483283 {A K : Type'} (f : type1470 A K) (y : K) : (term87 A K f y) = (f y).
Proof. exact (@lem4483282 K (A -> Prop) f y). Qed.
Lemma lem4483284 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term88 A K s t i) = (term89 A K s t i).
Proof. exact (@lem4483283 A K (term86 A K s t) i). Qed.
Lemma lem4483285 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term89 A K s t i) = (term90 A K s t i).
Proof. exact (eq_refl (term89 A K s t i)). Qed.
Lemma lem4483286 {A K : Type'} (s : type1470 A K) (t : type1470 A K) : (term91 A K s t) = (term86 A K s t).
Proof. exact (fun_ext (fun i : K => @lem4483285 A K s t i)). Qed.
Lemma lem4483287 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4483288 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term88 A K s t i) = (term89 A K s t i).
Proof. exact (MK_COMB (@lem4483286 A K s t) (@lem4483287 K i)). Qed.
Lemma lem4483289 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4483290 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term92 A K s t i) = (term93 A K s t i).
Proof. exact (MK_COMB (@lem4483289 A) (@lem4483288 A K s t i)). Qed.
Lemma lem4483291 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term89 A K s t i) = (term90 A K s t i).
Proof. exact (eq_refl (term89 A K s t i)). Qed.
Lemma lem4483292 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((term88 A K s t i) = (term89 A K s t i)) = ((term89 A K s t i) = (term90 A K s t i)).
Proof. exact (MK_COMB (@lem4483290 A K s t i) (@lem4483291 A K s t i)). Qed.
Lemma lem4483293 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term89 A K s t i) = (term90 A K s t i).
Proof. exact (EQ_MP (@lem4483292 A K s t i) (@lem4483284 A K s t i)). Qed.
Lemma lem4483294 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4483295 {A K : Type'} (x : A) (s : type1470 A K) (t : type1470 A K) (i : K) : (term94 A K x s t i) = (term95 A K x s t i).
Proof. exact (MK_COMB (@lem4483294 A x) (@lem4483293 A K s t i)). Qed.
Lemma lem4483297 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term18 A x s t) = (term19 A s x t).
Proof. exact (EQ_MP (@lem4483026 A s x t) (@lem4483025 A s t x)). Qed.
Lemma lem4483298 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term18 A x s t) = (term19 A s x t).
Proof. exact (@lem4483297 A s x t). Qed.
Lemma lem4483299 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term95 A K x s t i) = (term96 A K s x t i).
Proof. exact (@lem4483298 A (s i) x (t i)). Qed.
Lemma lem4483302 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term94 A K x s t i) = (term96 A K s x t i).
Proof. exact (TRANS (@lem4483295 A K x s t i) (@lem4483299 A K s x t i)). Qed.
Lemma lem4483303 {K : Type'} (i : K) (k : K -> Prop) : (term97 K i k) = (term97 K i k).
Proof. exact (eq_refl (term97 K i k)). Qed.
Lemma lem4483304 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term98 A K k x s t i) = (term99 A K k s x t i).
Proof. exact (MK_COMB (@lem4483303 K i k) (@lem4483302 A K s x t i)). Qed.
Lemma lem4483307 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4483308 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term100 A K GEN_PVAR_143 k x s t i) = (term101 A K GEN_PVAR_143 k s x t i).
Proof. exact (MK_COMB (@lem4483307 A K GEN_PVAR_143) (@lem4483304 A K k s x t i)). Qed.
Lemma lem4483309 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4483310 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term102 A K GEN_PVAR_143 k s t i x) = (term103 A K GEN_PVAR_143 k s t i x).
Proof. exact (MK_COMB (@lem4483308 A K GEN_PVAR_143 k s x t i) (@lem4483309 A K i x)). Qed.
Lemma lem4483311 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term104 A K GEN_PVAR_143 k s t i) = (term105 A K GEN_PVAR_143 k s t i).
Proof. exact (fun_ext (fun x : A => @lem4483310 A K GEN_PVAR_143 k s t i x)). Qed.
Lemma lem4483312 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4483313 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term106 A K GEN_PVAR_143 k s t i) = (term107 A K GEN_PVAR_143 k s t i).
Proof. exact (MK_COMB (@lem4483312 A) (@lem4483311 A K GEN_PVAR_143 k s t i)). Qed.
Lemma lem4483318 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term108 A K GEN_PVAR_143 k s t) = (term109 A K GEN_PVAR_143 k s t).
Proof. exact (fun_ext (fun i : K => @lem4483313 A K GEN_PVAR_143 k s t i)). Qed.
Lemma lem4483319 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4483320 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term110 A K GEN_PVAR_143 k s t) = (term111 A K GEN_PVAR_143 k s t).
Proof. exact (MK_COMB (@lem4483319 K) (@lem4483318 A K GEN_PVAR_143 k s t)). Qed.
Lemma lem4483325 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term112 A K k s t) = (term113 A K k s t).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4483320 A K GEN_PVAR_143 k s t)). Qed.
Lemma lem4483326 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4483327 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term85 A K k s t) = (term114 A K k s t).
Proof. exact (MK_COMB (@lem4483326 A K) (@lem4483325 A K k s t)). Qed.
Lemma lem4483328 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term30 A K k s t) = (term114 A K k s t).
Proof. exact (TRANS (@lem4483270 A K k s t) (@lem4483327 A K k s t)). Qed.
Lemma lem4483329 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4483330 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term115 A K x k s t) = (term116 A K x k s t).
Proof. exact (MK_COMB (@lem4483329 A K x) (@lem4483328 A K k s t)). Qed.
Lemma lem4483332 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem4483017 _83064 P x) (@lem4483016 _83064 P x)). Qed.
Lemma lem4483333 {A K : Type'} (P : type916 A K) (x : prod K A) : (term38 A K x P) = (term39 A K P x).
Proof. exact (@lem4483332 (prod K A) P x). Qed.
Lemma lem4483334 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term117 A K x k s t) = (term118 A K k s t x).
Proof. exact (@lem4483333 A K (term119 A K k s t) x). Qed.
Lemma lem4483335 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term120 A K k s t GEN_PVAR_143) = (term111 A K GEN_PVAR_143 k s t).
Proof. exact (eq_refl (term120 A K k s t GEN_PVAR_143)). Qed.
Lemma lem4483336 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term121 A K k s t) = (term113 A K k s t).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4483335 A K GEN_PVAR_143 k s t)). Qed.
Lemma lem4483337 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4483338 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term122 A K k s t) = (term114 A K k s t).
Proof. exact (MK_COMB (@lem4483337 A K) (@lem4483336 A K k s t)). Qed.
Lemma lem4483339 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4483340 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term117 A K x k s t) = (term116 A K x k s t).
Proof. exact (MK_COMB (@lem4483339 A K x) (@lem4483338 A K k s t)). Qed.
Lemma lem4483341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483342 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term123 A K x k s t) = (term124 A K x k s t).
Proof. exact (MK_COMB (@lem4483341) (@lem4483340 A K x k s t)). Qed.
Lemma lem4483343 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term118 A K k s t x) = (term125 A K x k s t).
Proof. exact (eq_refl (term118 A K k s t x)). Qed.
Lemma lem4483344 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term117 A K x k s t) = (term118 A K k s t x)) = ((term116 A K x k s t) = (term125 A K x k s t)).
Proof. exact (MK_COMB (@lem4483342 A K x k s t) (@lem4483343 A K x k s t)). Qed.
Lemma lem4483345 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term116 A K x k s t) = (term125 A K x k s t).
Proof. exact (EQ_MP (@lem4483344 A K x k s t) (@lem4483334 A K k s t x)). Qed.
Lemma lem4483355 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4483356 {A K : Type'} (f : type1534 A K) (y : Prop) : (term52 A K f y) = (f y).
Proof. exact (@lem4483355 Prop (type1223 A K) f y). Qed.
Lemma lem4483357 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (x' : A) (t : type1470 A K) (i : K) : (term126 A K x k s x' t i) = (term127 A K x k s x' t i).
Proof. exact (@lem4483356 A K (term55 A K x) (term99 A K k s x' t i)). Qed.
Lemma lem4483358 {A K : Type'} (p : Prop) (x : prod K A) : (term57 A K x p) = (term58 A K p x).
Proof. exact (eq_refl (term57 A K x p)). Qed.
Lemma lem4483359 {A K : Type'} (x : prod K A) : (term59 A K x) = (term55 A K x).
Proof. exact (fun_ext (fun p : Prop => @lem4483358 A K p x)). Qed.
Lemma lem4483360 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term99 A K k s x t i) = (term99 A K k s x t i).
Proof. exact (eq_refl (term99 A K k s x t i)). Qed.
Lemma lem4483361 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (x' : A) (t : type1470 A K) (i : K) : (term126 A K x k s x' t i) = (term127 A K x k s x' t i).
Proof. exact (MK_COMB (@lem4483359 A K x) (@lem4483360 A K k s x' t i)). Qed.
Lemma lem4483362 {A K : Type'} : (@eq ((prod K A) -> Prop)) = (@eq ((prod K A) -> Prop)).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop))). Qed.
Lemma lem4483363 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (x' : A) (t : type1470 A K) (i : K) : (term128 A K x k s x' t i) = (term129 A K x k s x' t i).
Proof. exact (MK_COMB (@lem4483362 A K) (@lem4483361 A K x k s x' t i)). Qed.
Lemma lem4483364 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term127 A K x' k s x t i) = (term130 A K k s x t i x').
Proof. exact (eq_refl (term127 A K x' k s x t i)). Qed.
Lemma lem4483365 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : ((term126 A K x' k s x t i) = (term127 A K x' k s x t i)) = ((term127 A K x' k s x t i) = (term130 A K k s x t i x')).
Proof. exact (MK_COMB (@lem4483363 A K x' k s x t i) (@lem4483364 A K k s x t i x')). Qed.
Lemma lem4483366 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term127 A K x' k s x t i) = (term130 A K k s x t i x').
Proof. exact (EQ_MP (@lem4483365 A K k s x t i x') (@lem4483357 A K x' k s x t i)). Qed.
Lemma lem4483377 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4483378 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term131 A K x k s t i x') = (term132 A K k s t x i x').
Proof. exact (MK_COMB (@lem4483366 A K k s x' t i x) (@lem4483377 A K i x')). Qed.
Lemma lem4483380 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4483381 {A K : Type'} (f : type1223 A K) (y : prod K A) : (term65 A K f y) = (f y).
Proof. exact (@lem4483380 (prod K A) Prop f y). Qed.
Lemma lem4483382 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term133 A K k s t x i x') = (term132 A K k s t x i x').
Proof. exact (@lem4483381 A K (term130 A K k s x' t i x) (@pair K A i x')). Qed.
Lemma lem4483383 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) (t' : prod K A) : (term134 A K k s x t i x' t') = (term135 A K k s x t i x' t').
Proof. exact (eq_refl (term134 A K k s x t i x' t')). Qed.
Lemma lem4483384 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term136 A K k s x t i x') = (term130 A K k s x t i x').
Proof. exact (fun_ext (fun t' : prod K A => @lem4483383 A K k s x t i x' t')). Qed.
Lemma lem4483385 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4483386 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term133 A K k s t x i x') = (term132 A K k s t x i x').
Proof. exact (MK_COMB (@lem4483384 A K k s x' t i x) (@lem4483385 A K i x')). Qed.
Lemma lem4483387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483388 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term137 A K k s t x i x') = (term138 A K k s t x i x').
Proof. exact (MK_COMB (@lem4483387) (@lem4483386 A K k s t x i x')). Qed.
Lemma lem4483389 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term132 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term132 A K k s t x i x')). Qed.
Lemma lem4483390 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term133 A K k s t x i x') = (term132 A K k s t x i x')) = ((term132 A K k s t x i x') = (term139 A K k s t x i x')).
Proof. exact (MK_COMB (@lem4483388 A K k s t x i x') (@lem4483389 A K k s t x i x')). Qed.
Lemma lem4483391 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term132 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (EQ_MP (@lem4483390 A K k s t x i x') (@lem4483382 A K k s t x i x')). Qed.
Lemma lem4483402 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term131 A K x k s t i x') = (term139 A K k s t x i x').
Proof. exact (TRANS (@lem4483378 A K k s t x i x') (@lem4483391 A K k s t x i x')). Qed.
Lemma lem4483403 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term140 A K x k s t i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4483402 A K k s t x i x')). Qed.
Lemma lem4483404 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4483405 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term142 A K x k s t i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4483404 A) (@lem4483403 A K k s t x i)). Qed.
Lemma lem4483410 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term144 A K x k s t) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4483405 A K k s t x i)). Qed.
Lemma lem4483411 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4483412 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term125 A K x k s t) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4483411 K) (@lem4483410 A K k s t x)). Qed.
Lemma lem4483417 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term116 A K x k s t) = (term146 A K k s t x).
Proof. exact (TRANS (@lem4483345 A K x k s t) (@lem4483412 A K k s t x)). Qed.
Lemma lem4483418 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term115 A K x k s t) = (term146 A K k s t x).
Proof. exact (TRANS (@lem4483330 A K x k s t) (@lem4483417 A K k s t x)). Qed.
Lemma lem4483419 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term34 A K x s k t) = (term115 A K x k s t)) = ((term82 A K s k t x) = (term146 A K k s t x)).
Proof. exact (MK_COMB (@lem4483266 A K s k t x) (@lem4483418 A K k s t x)). Qed.
Lemma lem4483424 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term147 A K k s t) = (term148 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4483419 A K k s t x)). Qed.
Lemma lem4483425 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4483426 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term31 A K k s t) = (term149 A K k s t).
Proof. exact (MK_COMB (@lem4483425 A K) (@lem4483424 A K k s t)). Qed.
Lemma lem4483431 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term29 A K s k t) = (term30 A K k s t)) = (term149 A K k s t).
Proof. exact (TRANS (@lem4483045 A K k s t) (@lem4483426 A K k s t)). Qed.
Lemma lem4483432 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term149 A K k s t) = ((term29 A K s k t) = (term30 A K k s t)).
Proof. exact (SYM (@lem4483431 A K k s t)). Qed.
Lemma lem4483434 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4483435 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term149 A K k s t) = (term151 A K k s t).
Proof. exact (@lem4483434 (term149 A K k s t)). Qed.
Lemma lem4483436 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term151 A K k s t) = (term149 A K k s t).
Proof. exact (SYM (@lem4483435 A K k s t)). Qed.
Lemma lem4483437 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term152 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4483438 {A K : Type'} : term153 A K.
Proof. exact (@lem47438 K A). Qed.
Lemma lem4483440 {A B K : Type'} : term154 A B K.
Proof. exact (@lem47438 (prod K A) B). Qed.
Lemma lem4483441 {A K : Type'} : term155 A K.
Proof. exact (@lem47438 A (prod K A)). Qed.
Lemma lem4483444 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) : term156 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4483445 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term157 A B K k s t.
Proof. exact (fun h0 : term156 A B K k s t => @lem4483444 A B K k s t h0). Qed.
Lemma lem4483446 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term157 A B K k s t) : term157 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4483447 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) : term156 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4483448 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) (h2 : term157 A B K k s t) : term156 A B K k s t.
Proof. exact (@lem4483446 A B K k s t h2 (@lem4483447 A B K k s t h1)). Qed.
Lemma lem4483449 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) : term158 A B K k s t.
Proof. exact (fun h0 : term157 A B K k s t => @lem4483448 A B K k s t h1 h0). Qed.
Lemma lem4483450 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term157 A B K k s t) : term157 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4483451 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) (h2 : term157 A B K k s t) : term156 A B K k s t.
Proof. exact (@lem4483449 A B K k s t h1 (@lem4483450 A B K k s t h2)). Qed.
Lemma lem4483452 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term157 A B K k s t) : term157 A B K k s t.
Proof. exact (fun h0 : term156 A B K k s t => @lem4483451 A B K k s t h0 h1). Qed.
Lemma lem4483453 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term159 A B K k s t.
Proof. exact (fun h0 : term157 A B K k s t => @lem4483452 A B K k s t h0). Qed.
Lemma lem4483456 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term157 A B K k s t.
Proof. exact (@lem4483453 A B K k s t (@lem4483445 A B K k s t)). Qed.
Lemma lem4483457 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term157 A B K k s t.
Proof. exact (@lem4483456 A B K k s t). Qed.
Lemma lem4483689 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4483690 {A B K : Type'} : (term160 A B K) = (term161 A B K).
Proof. exact (@lem4483689 (term154 A B K)). Qed.
Lemma lem4483709 {A K : Type'} : (term162 A K) = (term162 A K).
Proof. exact (eq_refl (term162 A K)). Qed.
Lemma lem4483710 {A B K : Type'} : (term163 A B K) = (term164 A B K).
Proof. exact (MK_COMB (@lem4483709 A K) (@lem4483690 A B K)). Qed.
Lemma lem4483713 {A K : Type'} : (term165 A K) = (term165 A K).
Proof. exact (eq_refl (term165 A K)). Qed.
Lemma lem4483714 {A B K : Type'} : (term166 A B K) = (term167 A B K).
Proof. exact (MK_COMB (@lem4483713 A K) (@lem4483710 A B K)). Qed.
Lemma lem4483717 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term168 A K k s t) = (term168 A K k s t).
Proof. exact (eq_refl (term168 A K k s t)). Qed.
Lemma lem4483718 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term156 A B K k s t) = (term169 A B K k s t).
Proof. exact (MK_COMB (@lem4483717 A K k s t) (@lem4483714 A B K)). Qed.
Lemma lem4483721 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term170 A B K s t) = (term171 A B K s t).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4483718 A B K k s t)). Qed.
Lemma lem4483722 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4483723 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term172 A B K s t) = (term173 A B K s t).
Proof. exact (MK_COMB (@lem4483722 K) (@lem4483721 A B K s t)). Qed.
Lemma lem4483728 {A B K : Type'} (t : type1470 A K) : (term174 A B K t) = (term175 A B K t).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4483723 A B K s t)). Qed.
Lemma lem4483729 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4483730 {A B K : Type'} (t : type1470 A K) : (term176 A B K t) = (term177 A B K t).
Proof. exact (MK_COMB (@lem4483729 A K) (@lem4483728 A B K t)). Qed.
Lemma lem4483735 {A B K : Type'} : (term178 A B K) = (term179 A B K).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4483730 A B K t)). Qed.
Lemma lem4483736 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4483745 {A B K : Type'} : (term180 A B K) = (term181 A B K).
Proof. exact (MK_COMB (@lem4483736 A K) (@lem4483735 A B K)). Qed.
Lemma lem4483754 {A B K : Type'} (x : prod K A) (a : prod K A) (y : B) (b : B) : (((@pair (prod K A) B x y) = (@pair (prod K A) B a b)) = (term182 A B K x a y b)) = (((@pair (prod K A) B x y) = (@pair (prod K A) B a b)) = (term182 A B K x a y b)).
Proof. exact (eq_refl (((@pair (prod K A) B x y) = (@pair (prod K A) B a b)) = (term182 A B K x a y b))). Qed.
Lemma lem4483755 {A B K : Type'} (x : prod K A) (a : prod K A) (y : B) : (term183 A B K x a y) = (term183 A B K x a y).
Proof. exact (fun_ext (fun b : B => @lem4483754 A B K x a y b)). Qed.
Lemma lem4483756 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4483757 {A B K : Type'} (x : prod K A) (a : prod K A) (y : B) : (term184 A B K x a y) = (term184 A B K x a y).
Proof. exact (MK_COMB (@lem4483756 B) (@lem4483755 A B K x a y)). Qed.
Lemma lem4483758 {A B K : Type'} (x : prod K A) (y : B) : (term185 A B K x y) = (term185 A B K x y).
Proof. exact (fun_ext (fun a : prod K A => @lem4483757 A B K x a y)). Qed.
Lemma lem4483759 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4483760 {A B K : Type'} (x : prod K A) (y : B) : (term186 A B K x y) = (term186 A B K x y).
Proof. exact (MK_COMB (@lem4483759 A K) (@lem4483758 A B K x y)). Qed.
Lemma lem4483761 {A B K : Type'} (x : prod K A) : (term187 A B K x) = (term187 A B K x).
Proof. exact (fun_ext (fun y : B => @lem4483760 A B K x y)). Qed.
Lemma lem4483762 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4483763 {A B K : Type'} (x : prod K A) : (term188 A B K x) = (term188 A B K x).
Proof. exact (MK_COMB (@lem4483762 B) (@lem4483761 A B K x)). Qed.
Lemma lem4483764 {A B K : Type'} : (term189 A B K) = (term189 A B K).
Proof. exact (fun_ext (fun x : prod K A => @lem4483763 A B K x)). Qed.
Lemma lem4483765 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4483766 {A B K : Type'} : (term154 A B K) = (term154 A B K).
Proof. exact (MK_COMB (@lem4483765 A K) (@lem4483764 A B K)). Qed.
Lemma lem4483767 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4483768 {A B K : Type'} : (term161 A B K) = (term161 A B K).
Proof. exact (MK_COMB (@lem4483767) (@lem4483766 A B K)). Qed.
Lemma lem4483777 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b)) = (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b)).
Proof. exact (eq_refl (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b))). Qed.
Lemma lem4483778 {A K : Type'} (x : K) (a : K) (y : A) : (term191 A K x a y) = (term191 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4483777 A K x a y b)). Qed.
Lemma lem4483779 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4483780 {A K : Type'} (x : K) (a : K) (y : A) : (term192 A K x a y) = (term192 A K x a y).
Proof. exact (MK_COMB (@lem4483779 A) (@lem4483778 A K x a y)). Qed.
Lemma lem4483781 {A K : Type'} (x : K) (y : A) : (term193 A K x y) = (term193 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4483780 A K x a y)). Qed.
Lemma lem4483782 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4483783 {A K : Type'} (x : K) (y : A) : (term194 A K x y) = (term194 A K x y).
Proof. exact (MK_COMB (@lem4483782 K) (@lem4483781 A K x y)). Qed.
Lemma lem4483784 {A K : Type'} (x : K) : (term195 A K x) = (term195 A K x).
Proof. exact (fun_ext (fun y : A => @lem4483783 A K x y)). Qed.
Lemma lem4483785 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4483786 {A K : Type'} (x : K) : (term196 A K x) = (term196 A K x).
Proof. exact (MK_COMB (@lem4483785 A) (@lem4483784 A K x)). Qed.
Lemma lem4483787 {A K : Type'} : (term197 A K) = (term197 A K).
Proof. exact (fun_ext (fun x : K => @lem4483786 A K x)). Qed.
Lemma lem4483788 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4483789 {A K : Type'} : (term153 A K) = (term153 A K).
Proof. exact (MK_COMB (@lem4483788 K) (@lem4483787 A K)). Qed.
Lemma lem4483790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4483791 {A K : Type'} : (term162 A K) = (term162 A K).
Proof. exact (MK_COMB (@lem4483790) (@lem4483789 A K)). Qed.
Lemma lem4483792 {A B K : Type'} : (term164 A B K) = (term164 A B K).
Proof. exact (MK_COMB (@lem4483791 A K) (@lem4483768 A B K)). Qed.
Lemma lem4483801 {A K : Type'} (x : A) (a : A) (y : prod K A) (b : prod K A) : (((@pair A (prod K A) x y) = (@pair A (prod K A) a b)) = (term198 A K x a y b)) = (((@pair A (prod K A) x y) = (@pair A (prod K A) a b)) = (term198 A K x a y b)).
Proof. exact (eq_refl (((@pair A (prod K A) x y) = (@pair A (prod K A) a b)) = (term198 A K x a y b))). Qed.
Lemma lem4483802 {A K : Type'} (x : A) (a : A) (y : prod K A) : (term199 A K x a y) = (term199 A K x a y).
Proof. exact (fun_ext (fun b : prod K A => @lem4483801 A K x a y b)). Qed.
Lemma lem4483803 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4483804 {A K : Type'} (x : A) (a : A) (y : prod K A) : (term200 A K x a y) = (term200 A K x a y).
Proof. exact (MK_COMB (@lem4483803 A K) (@lem4483802 A K x a y)). Qed.
Lemma lem4483805 {A K : Type'} (x : A) (y : prod K A) : (term201 A K x y) = (term201 A K x y).
Proof. exact (fun_ext (fun a : A => @lem4483804 A K x a y)). Qed.
Lemma lem4483806 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4483807 {A K : Type'} (x : A) (y : prod K A) : (term202 A K x y) = (term202 A K x y).
Proof. exact (MK_COMB (@lem4483806 A) (@lem4483805 A K x y)). Qed.
Lemma lem4483808 {A K : Type'} (x : A) : (term203 A K x) = (term203 A K x).
Proof. exact (fun_ext (fun y : prod K A => @lem4483807 A K x y)). Qed.
Lemma lem4483809 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4483810 {A K : Type'} (x : A) : (term204 A K x) = (term204 A K x).
Proof. exact (MK_COMB (@lem4483809 A K) (@lem4483808 A K x)). Qed.
Lemma lem4483811 {A K : Type'} : (term205 A K) = (term205 A K).
Proof. exact (fun_ext (fun x : A => @lem4483810 A K x)). Qed.
Lemma lem4483812 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4483813 {A K : Type'} : (term155 A K) = (term155 A K).
Proof. exact (MK_COMB (@lem4483812 A) (@lem4483811 A K)). Qed.
Lemma lem4483814 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4483815 {A K : Type'} : (term165 A K) = (term165 A K).
Proof. exact (MK_COMB (@lem4483814) (@lem4483813 A K)). Qed.
Lemma lem4483816 {A B K : Type'} : (term167 A B K) = (term167 A B K).
Proof. exact (MK_COMB (@lem4483815 A K) (@lem4483792 A B K)). Qed.
Lemma lem4483829 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term139 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term139 A K k s t x i x')). Qed.
Lemma lem4483830 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term141 A K k s t x i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4483829 A K k s t x i x')). Qed.
Lemma lem4483831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4483832 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term143 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4483831 A) (@lem4483830 A K k s t x i)). Qed.
Lemma lem4483833 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term145 A K k s t x) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4483832 A K k s t x i)). Qed.
Lemma lem4483834 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4483835 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term146 A K k s t x) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4483834 K) (@lem4483833 A K k s t x)). Qed.
Lemma lem4483844 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term72 A K k t x i x')). Qed.
Lemma lem4483845 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term74 A K k t x i) = (term74 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4483844 A K k t x i x')). Qed.
Lemma lem4483846 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4483847 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term76 A K k t x i) = (term76 A K k t x i).
Proof. exact (MK_COMB (@lem4483846 A) (@lem4483845 A K k t x i)). Qed.
Lemma lem4483848 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term78 A K k t x) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4483847 A K k t x i)). Qed.
Lemma lem4483849 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4483850 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4483849 K) (@lem4483848 A K k t x)). Qed.
Lemma lem4483859 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term72 A K k s x i x')). Qed.
Lemma lem4483860 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term74 A K k s x i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4483859 A K k s x i x')). Qed.
Lemma lem4483861 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4483862 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term76 A K k s x i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4483861 A) (@lem4483860 A K k s x i)). Qed.
Lemma lem4483863 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term78 A K k s x) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4483862 A K k s x i)). Qed.
Lemma lem4483864 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4483865 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term79 A K k s x) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4483864 K) (@lem4483863 A K k s x)). Qed.
Lemma lem4483866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4483867 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term81 A K k s x) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4483866) (@lem4483865 A K k s x)). Qed.
Lemma lem4483868 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4483867 A K k s x) (@lem4483850 A K k t x)). Qed.
Lemma lem4483869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4483870 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term84 A K s k t x) = (term84 A K s k t x).
Proof. exact (MK_COMB (@lem4483869) (@lem4483868 A K s k t x)). Qed.
Lemma lem4483871 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term82 A K s k t x) = (term146 A K k s t x)) = ((term82 A K s k t x) = (term146 A K k s t x)).
Proof. exact (MK_COMB (@lem4483870 A K s k t x) (@lem4483835 A K k s t x)). Qed.
Lemma lem4483872 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term148 A K k s t) = (term148 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4483871 A K k s t x)). Qed.
Lemma lem4483873 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4483874 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term149 A K k s t) = (term149 A K k s t).
Proof. exact (MK_COMB (@lem4483873 A K) (@lem4483872 A K k s t)). Qed.
Lemma lem4483875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4483876 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term152 A K k s t).
Proof. exact (MK_COMB (@lem4483875) (@lem4483874 A K k s t)). Qed.
Lemma lem4483877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4483878 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term168 A K k s t) = (term168 A K k s t).
Proof. exact (MK_COMB (@lem4483877) (@lem4483876 A K k s t)). Qed.
Lemma lem4483879 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term169 A B K k s t) = (term169 A B K k s t).
Proof. exact (MK_COMB (@lem4483878 A K k s t) (@lem4483816 A B K)). Qed.
Lemma lem4483880 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term171 A B K s t) = (term171 A B K s t).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4483879 A B K k s t)). Qed.
Lemma lem4483881 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4483882 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term173 A B K s t) = (term173 A B K s t).
Proof. exact (MK_COMB (@lem4483881 K) (@lem4483880 A B K s t)). Qed.
Lemma lem4483883 {A B K : Type'} (t : type1470 A K) : (term175 A B K t) = (term175 A B K t).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4483882 A B K s t)). Qed.
Lemma lem4483884 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4483885 {A B K : Type'} (t : type1470 A K) : (term177 A B K t) = (term177 A B K t).
Proof. exact (MK_COMB (@lem4483884 A K) (@lem4483883 A B K t)). Qed.
Lemma lem4483886 {A B K : Type'} : (term179 A B K) = (term179 A B K).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4483885 A B K t)). Qed.
Lemma lem4483887 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4483888 {A B K : Type'} : (term181 A B K) = (term181 A B K).
Proof. exact (MK_COMB (@lem4483887 A K) (@lem4483886 A B K)). Qed.
Lemma lem4484051 {A B K : Type'} : (term180 A B K) = (term181 A B K).
Proof. exact (TRANS (@lem4483745 A B K) (@lem4483888 A B K)). Qed.
Lemma lem4484052 {A B K : Type'} : (term181 A B K) = (term180 A B K).
Proof. exact (SYM (@lem4484051 A B K)). Qed.
Lemma lem4484053 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term152 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4484065 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term206 A K k x s i) = (term207 A K k x s i).
Proof. exact (@lem17045 (@IN K i k) (term208 A K x s i)). Qed.
Lemma lem4484069 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4484071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484072 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term210 A K k x s i) = (term211 A K k x s i).
Proof. exact (MK_COMB (@lem4484071) (@lem4484065 A K k x s i)). Qed.
Lemma lem4484073 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term212 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (MK_COMB (@lem4484072 A K k x' s i) (@lem4484069 A K x i x')). Qed.
Lemma lem4484074 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k s x i x') = (term212 A K k s x i x').
Proof. exact (@lem17045 (term56 A K k x' s i) (x = (@pair K A i x'))). Qed.
Lemma lem4484075 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (TRANS (@lem4484074 A K k s x i x') (@lem4484073 A K k s x i x')). Qed.
Lemma lem4484078 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term72 A K k s x i x')). Qed.
Lemma lem4484079 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4484080 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term217 A K k s x i) = (term218 A K k s x i).
Proof. exact (@lem4484079 A (term74 A K k s x i)). Qed.
Lemma lem4484081 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term219 A K k s x i x')). Qed.
Lemma lem4484082 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4484083 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k s x i x') = (term214 A K k s x i x').
Proof. exact (MK_COMB (@lem4484082) (@lem4484081 A K k s x i x')). Qed.
Lemma lem4484084 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (TRANS (@lem4484083 A K k s x i x') (@lem4484075 A K k s x i x')). Qed.
Lemma lem4484085 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term221 A K k s x i) = (term222 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4484084 A K k s x i x')). Qed.
Lemma lem4484086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4484087 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term218 A K k s x i) = (term223 A K k s x i).
Proof. exact (MK_COMB (@lem4484086 A) (@lem4484085 A K k s x i)). Qed.
Lemma lem4484088 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term217 A K k s x i) = (term223 A K k s x i).
Proof. exact (TRANS (@lem4484080 A K k s x i) (@lem4484087 A K k s x i)). Qed.
Lemma lem4484089 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term74 A K k s x i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4484078 A K k s x i x')). Qed.
Lemma lem4484090 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484091 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term76 A K k s x i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4484090 A) (@lem4484089 A K k s x i)). Qed.
Lemma lem4484092 {K : Type'} (P : K -> Prop) : (term215 K P) = (term216 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem4484093 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term224 A K k s x) = (term225 A K k s x).
Proof. exact (@lem4484092 K (term78 A K k s x)). Qed.
Lemma lem4484094 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term226 A K k s x i) = (term76 A K k s x i).
Proof. exact (eq_refl (term226 A K k s x i)). Qed.
Lemma lem4484095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4484096 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term227 A K k s x i) = (term217 A K k s x i).
Proof. exact (MK_COMB (@lem4484095) (@lem4484094 A K k s x i)). Qed.
Lemma lem4484097 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term227 A K k s x i) = (term223 A K k s x i).
Proof. exact (TRANS (@lem4484096 A K k s x i) (@lem4484088 A K k s x i)). Qed.
Lemma lem4484098 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term228 A K k s x) = (term229 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4484097 A K k s x i)). Qed.
Lemma lem4484099 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4484100 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term225 A K k s x) = (term230 A K k s x).
Proof. exact (MK_COMB (@lem4484099 K) (@lem4484098 A K k s x)). Qed.
Lemma lem4484101 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term224 A K k s x) = (term230 A K k s x).
Proof. exact (TRANS (@lem4484093 A K k s x) (@lem4484100 A K k s x)). Qed.
Lemma lem4484102 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term78 A K k s x) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4484091 A K k s x i)). Qed.
Lemma lem4484103 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484104 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term79 A K k s x) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4484103 K) (@lem4484102 A K k s x)). Qed.
Lemma lem4484113 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term206 A K k x t i) = (term207 A K k x t i).
Proof. exact (@lem17045 (@IN K i k) (term208 A K x t i)). Qed.
Lemma lem4484117 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4484119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484120 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term210 A K k x t i) = (term211 A K k x t i).
Proof. exact (MK_COMB (@lem4484119) (@lem4484113 A K k x t i)). Qed.
Lemma lem4484121 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term212 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (MK_COMB (@lem4484120 A K k x' t i) (@lem4484117 A K x i x')). Qed.
Lemma lem4484122 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k t x i x') = (term212 A K k t x i x').
Proof. exact (@lem17045 (term56 A K k x' t i) (x = (@pair K A i x'))). Qed.
Lemma lem4484123 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (TRANS (@lem4484122 A K k t x i x') (@lem4484121 A K k t x i x')). Qed.
Lemma lem4484126 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term72 A K k t x i x')). Qed.
Lemma lem4484127 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4484128 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term217 A K k t x i) = (term218 A K k t x i).
Proof. exact (@lem4484127 A (term74 A K k t x i)). Qed.
Lemma lem4484129 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term219 A K k t x i x')). Qed.
Lemma lem4484130 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4484131 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k t x i x') = (term214 A K k t x i x').
Proof. exact (MK_COMB (@lem4484130) (@lem4484129 A K k t x i x')). Qed.
Lemma lem4484132 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (TRANS (@lem4484131 A K k t x i x') (@lem4484123 A K k t x i x')). Qed.
Lemma lem4484133 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term221 A K k t x i) = (term222 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484132 A K k t x i x')). Qed.
Lemma lem4484134 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4484135 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term218 A K k t x i) = (term223 A K k t x i).
Proof. exact (MK_COMB (@lem4484134 A) (@lem4484133 A K k t x i)). Qed.
Lemma lem4484136 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term217 A K k t x i) = (term223 A K k t x i).
Proof. exact (TRANS (@lem4484128 A K k t x i) (@lem4484135 A K k t x i)). Qed.
Lemma lem4484137 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term74 A K k t x i) = (term74 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484126 A K k t x i x')). Qed.
Lemma lem4484138 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484139 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term76 A K k t x i) = (term76 A K k t x i).
Proof. exact (MK_COMB (@lem4484138 A) (@lem4484137 A K k t x i)). Qed.
Lemma lem4484140 {K : Type'} (P : K -> Prop) : (term215 K P) = (term216 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem4484141 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term224 A K k t x) = (term225 A K k t x).
Proof. exact (@lem4484140 K (term78 A K k t x)). Qed.
Lemma lem4484142 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term226 A K k t x i) = (term76 A K k t x i).
Proof. exact (eq_refl (term226 A K k t x i)). Qed.
Lemma lem4484143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4484144 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term227 A K k t x i) = (term217 A K k t x i).
Proof. exact (MK_COMB (@lem4484143) (@lem4484142 A K k t x i)). Qed.
Lemma lem4484145 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term227 A K k t x i) = (term223 A K k t x i).
Proof. exact (TRANS (@lem4484144 A K k t x i) (@lem4484136 A K k t x i)). Qed.
Lemma lem4484146 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term228 A K k t x) = (term229 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4484145 A K k t x i)). Qed.
Lemma lem4484147 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4484148 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term225 A K k t x) = (term230 A K k t x).
Proof. exact (MK_COMB (@lem4484147 K) (@lem4484146 A K k t x)). Qed.
Lemma lem4484149 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term224 A K k t x) = (term230 A K k t x).
Proof. exact (TRANS (@lem4484141 A K k t x) (@lem4484148 A K k t x)). Qed.
Lemma lem4484150 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term78 A K k t x) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4484139 A K k t x i)). Qed.
Lemma lem4484151 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484152 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4484151 K) (@lem4484150 A K k t x)). Qed.
Lemma lem4484153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484154 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term231 A K k s x) = (term232 A K k s x).
Proof. exact (MK_COMB (@lem4484153) (@lem4484101 A K k s x)). Qed.
Lemma lem4484155 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term233 A K s k t x) = (term234 A K s k t x).
Proof. exact (MK_COMB (@lem4484154 A K k s x) (@lem4484149 A K k t x)). Qed.
Lemma lem4484156 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term235 A K s k t x) = (term233 A K s k t x).
Proof. exact (@lem17160 (term79 A K k s x) (term79 A K k t x)). Qed.
Lemma lem4484157 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term235 A K s k t x) = (term234 A K s k t x).
Proof. exact (TRANS (@lem4484156 A K s k t x) (@lem4484155 A K s k t x)). Qed.
Lemma lem4484158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484159 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term81 A K k s x) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4484158) (@lem4484104 A K k s x)). Qed.
Lemma lem4484160 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4484159 A K k s x) (@lem4484152 A K k t x)). Qed.
Lemma lem4484171 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term236 A K s x t i) = (term237 A K s x t i).
Proof. exact (@lem17160 (term208 A K x s i) (term208 A K x t i)). Qed.
Lemma lem4484176 {K : Type'} (i : K) (k : K -> Prop) : (term238 K i k) = (term238 K i k).
Proof. exact (eq_refl (term238 K i k)). Qed.
Lemma lem4484177 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term239 A K k s x t i) = (term240 A K k s x t i).
Proof. exact (MK_COMB (@lem4484176 K i k) (@lem4484171 A K s x t i)). Qed.
Lemma lem4484178 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term241 A K k s x t i) = (term239 A K k s x t i).
Proof. exact (@lem17045 (@IN K i k) (term96 A K s x t i)). Qed.
Lemma lem4484179 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term241 A K k s x t i) = (term240 A K k s x t i).
Proof. exact (TRANS (@lem4484178 A K k s x t i) (@lem4484177 A K k s x t i)). Qed.
Lemma lem4484183 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4484185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484186 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term242 A K k s x t i) = (term243 A K k s x t i).
Proof. exact (MK_COMB (@lem4484185) (@lem4484179 A K k s x t i)). Qed.
Lemma lem4484187 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term244 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (MK_COMB (@lem4484186 A K k s x' t i) (@lem4484183 A K x i x')). Qed.
Lemma lem4484188 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term246 A K k s t x i x') = (term244 A K k s t x i x').
Proof. exact (@lem17045 (term99 A K k s x' t i) (x = (@pair K A i x'))). Qed.
Lemma lem4484189 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term246 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (TRANS (@lem4484188 A K k s t x i x') (@lem4484187 A K k s t x i x')). Qed.
Lemma lem4484192 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term139 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term139 A K k s t x i x')). Qed.
Lemma lem4484193 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4484194 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term247 A K k s t x i) = (term248 A K k s t x i).
Proof. exact (@lem4484193 A (term141 A K k s t x i)). Qed.
Lemma lem4484195 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term249 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term249 A K k s t x i x')). Qed.
Lemma lem4484196 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4484197 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term250 A K k s t x i x') = (term246 A K k s t x i x').
Proof. exact (MK_COMB (@lem4484196) (@lem4484195 A K k s t x i x')). Qed.
Lemma lem4484198 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term250 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (TRANS (@lem4484197 A K k s t x i x') (@lem4484189 A K k s t x i x')). Qed.
Lemma lem4484199 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term251 A K k s t x i) = (term252 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484198 A K k s t x i x')). Qed.
Lemma lem4484200 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4484201 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term248 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (MK_COMB (@lem4484200 A) (@lem4484199 A K k s t x i)). Qed.
Lemma lem4484202 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term247 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (TRANS (@lem4484194 A K k s t x i) (@lem4484201 A K k s t x i)). Qed.
Lemma lem4484203 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term141 A K k s t x i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484192 A K k s t x i x')). Qed.
Lemma lem4484204 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484205 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term143 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4484204 A) (@lem4484203 A K k s t x i)). Qed.
Lemma lem4484206 {K : Type'} (P : K -> Prop) : (term215 K P) = (term216 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem4484207 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term254 A K k s t x) = (term255 A K k s t x).
Proof. exact (@lem4484206 K (term145 A K k s t x)). Qed.
Lemma lem4484208 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term256 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (eq_refl (term256 A K k s t x i)). Qed.
Lemma lem4484209 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4484210 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term257 A K k s t x i) = (term247 A K k s t x i).
Proof. exact (MK_COMB (@lem4484209) (@lem4484208 A K k s t x i)). Qed.
Lemma lem4484211 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term257 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (TRANS (@lem4484210 A K k s t x i) (@lem4484202 A K k s t x i)). Qed.
Lemma lem4484212 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term258 A K k s t x) = (term259 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484211 A K k s t x i)). Qed.
Lemma lem4484213 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4484214 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term255 A K k s t x) = (term260 A K k s t x).
Proof. exact (MK_COMB (@lem4484213 K) (@lem4484212 A K k s t x)). Qed.
Lemma lem4484215 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term254 A K k s t x) = (term260 A K k s t x).
Proof. exact (TRANS (@lem4484207 A K k s t x) (@lem4484214 A K k s t x)). Qed.
Lemma lem4484216 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term145 A K k s t x) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484205 A K k s t x i)). Qed.
Lemma lem4484217 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484218 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term146 A K k s t x) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4484217 K) (@lem4484216 A K k s t x)). Qed.
Lemma lem4484219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484220 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term261 A K s k t x) = (term262 A K s k t x).
Proof. exact (MK_COMB (@lem4484219) (@lem4484157 A K s k t x)). Qed.
Lemma lem4484221 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term263 A K k s t x) = (term264 A K k s t x).
Proof. exact (MK_COMB (@lem4484220 A K s k t x) (@lem4484218 A K k s t x)). Qed.
Lemma lem4484222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484223 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term265 A K s k t x) = (term265 A K s k t x).
Proof. exact (MK_COMB (@lem4484222) (@lem4484160 A K s k t x)). Qed.
Lemma lem4484224 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term266 A K k s t x) = (term267 A K k s t x).
Proof. exact (MK_COMB (@lem4484223 A K s k t x) (@lem4484215 A K k s t x)). Qed.
Lemma lem4484225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484226 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term268 A K k s t x) = (term269 A K k s t x).
Proof. exact (MK_COMB (@lem4484225) (@lem4484224 A K k s t x)). Qed.
Lemma lem4484227 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term270 A K k s t x) = (term271 A K k s t x).
Proof. exact (MK_COMB (@lem4484226 A K k s t x) (@lem4484221 A K k s t x)). Qed.
Lemma lem4484228 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term272 A K k s t x) = (term270 A K k s t x).
Proof. exact (@lem17646 (term82 A K s k t x) (term146 A K k s t x)). Qed.
Lemma lem4484229 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term272 A K k s t x) = (term271 A K k s t x).
Proof. exact (TRANS (@lem4484228 A K k s t x) (@lem4484227 A K k s t x)). Qed.
Lemma lem4484230 {A K : Type'} (P : type1223 A K) : (term273 A K P) = (term274 A K P).
Proof. exact (@lem18392 (prod K A) P). Qed.
Lemma lem4484231 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term275 A K k s t).
Proof. exact (@lem4484230 A K (term148 A K k s t)). Qed.
Lemma lem4484232 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term276 A K k s t x) = ((term82 A K s k t x) = (term146 A K k s t x)).
Proof. exact (eq_refl (term276 A K k s t x)). Qed.
Lemma lem4484233 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4484234 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term277 A K k s t x) = (term272 A K k s t x).
Proof. exact (MK_COMB (@lem4484233) (@lem4484232 A K k s t x)). Qed.
Lemma lem4484235 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term277 A K k s t x) = (term271 A K k s t x).
Proof. exact (TRANS (@lem4484234 A K k s t x) (@lem4484229 A K k s t x)). Qed.
Lemma lem4484236 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term278 A K k s t) = (term279 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484235 A K k s t x)). Qed.
Lemma lem4484237 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484238 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term275 A K k s t) = (term280 A K k s t).
Proof. exact (MK_COMB (@lem4484237 A K) (@lem4484236 A K k s t)). Qed.
Lemma lem4484239 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term280 A K k s t).
Proof. exact (TRANS (@lem4484231 A K k s t) (@lem4484238 A K k s t)). Qed.
Lemma lem4484241 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4484242 {A K : Type'} (P : type1223 A K) (Q : type1223 A K) : (term283 A K P Q) = (term284 A K P Q).
Proof. exact (@lem4484241 (prod K A) P Q). Qed.
Lemma lem4484243 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term285 A K k s t) = (term286 A K k s t).
Proof. exact (@lem4484242 A K (term287 A K k s t) (term288 A K k s t)). Qed.
Lemma lem4484244 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term289 A K k s t x) = (term267 A K k s t x).
Proof. exact (eq_refl (term289 A K k s t x)). Qed.
Lemma lem4484245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484246 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term290 A K k s t x) = (term269 A K k s t x).
Proof. exact (MK_COMB (@lem4484245) (@lem4484244 A K k s t x)). Qed.
Lemma lem4484247 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term291 A K k s t x) = (term264 A K k s t x).
Proof. exact (eq_refl (term291 A K k s t x)). Qed.
Lemma lem4484248 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term292 A K k s t x) = (term271 A K k s t x).
Proof. exact (MK_COMB (@lem4484246 A K k s t x) (@lem4484247 A K k s t x)). Qed.
Lemma lem4484249 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term293 A K k s t) = (term279 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484248 A K k s t x)). Qed.
Lemma lem4484250 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484251 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term285 A K k s t) = (term280 A K k s t).
Proof. exact (MK_COMB (@lem4484250 A K) (@lem4484249 A K k s t)). Qed.
Lemma lem4484252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484253 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term294 A K k s t) = (term295 A K k s t).
Proof. exact (MK_COMB (@lem4484252) (@lem4484251 A K k s t)). Qed.
Lemma lem4484254 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term289 A K k s t x) = (term267 A K k s t x).
Proof. exact (eq_refl (term289 A K k s t x)). Qed.
Lemma lem4484255 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term296 A K k s t) = (term287 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484254 A K k s t x)). Qed.
Lemma lem4484256 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484257 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term297 A K k s t) = (term298 A K k s t).
Proof. exact (MK_COMB (@lem4484256 A K) (@lem4484255 A K k s t)). Qed.
Lemma lem4484258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484259 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term299 A K k s t) = (term300 A K k s t).
Proof. exact (MK_COMB (@lem4484258) (@lem4484257 A K k s t)). Qed.
Lemma lem4484260 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term291 A K k s t x) = (term264 A K k s t x).
Proof. exact (eq_refl (term291 A K k s t x)). Qed.
Lemma lem4484261 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term301 A K k s t) = (term288 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484260 A K k s t x)). Qed.
Lemma lem4484262 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484263 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term302 A K k s t) = (term303 A K k s t).
Proof. exact (MK_COMB (@lem4484262 A K) (@lem4484261 A K k s t)). Qed.
Lemma lem4484264 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term286 A K k s t) = (term304 A K k s t).
Proof. exact (MK_COMB (@lem4484259 A K k s t) (@lem4484263 A K k s t)). Qed.
Lemma lem4484265 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term285 A K k s t) = (term286 A K k s t)) = ((term280 A K k s t) = (term304 A K k s t)).
Proof. exact (MK_COMB (@lem4484253 A K k s t) (@lem4484264 A K k s t)). Qed.
Lemma lem4484266 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term280 A K k s t) = (term304 A K k s t).
Proof. exact (EQ_MP (@lem4484265 A K k s t) (@lem4484243 A K k s t)). Qed.
Lemma lem4484676 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4484677 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term282 K P Q) = (term281 K P Q).
Proof. exact (@lem4484676 K P Q). Qed.
Lemma lem4484678 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term305 A K s k t x) = (term306 A K s k t x).
Proof. exact (@lem4484677 K (term78 A K k s x) (term78 A K k t x)). Qed.
Lemma lem4484679 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term226 A K k s x i) = (term76 A K k s x i).
Proof. exact (eq_refl (term226 A K k s x i)). Qed.
Lemma lem4484680 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term307 A K k s x) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4484679 A K k s x i)). Qed.
Lemma lem4484681 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484682 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term308 A K k s x) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4484681 K) (@lem4484680 A K k s x)). Qed.
Lemma lem4484683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484684 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term309 A K k s x) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4484683) (@lem4484682 A K k s x)). Qed.
Lemma lem4484685 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term226 A K k t x i) = (term76 A K k t x i).
Proof. exact (eq_refl (term226 A K k t x i)). Qed.
Lemma lem4484686 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term307 A K k t x) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4484685 A K k t x i)). Qed.
Lemma lem4484687 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484688 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term308 A K k t x) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4484687 K) (@lem4484686 A K k t x)). Qed.
Lemma lem4484689 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term305 A K s k t x) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4484684 A K k s x) (@lem4484688 A K k t x)). Qed.
Lemma lem4484690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484691 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term310 A K s k t x) = (term84 A K s k t x).
Proof. exact (MK_COMB (@lem4484690) (@lem4484689 A K s k t x)). Qed.
Lemma lem4484692 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term226 A K k s x i) = (term76 A K k s x i).
Proof. exact (eq_refl (term226 A K k s x i)). Qed.
Lemma lem4484693 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484694 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term311 A K k s x i) = (term312 A K k s x i).
Proof. exact (MK_COMB (@lem4484693) (@lem4484692 A K k s x i)). Qed.
Lemma lem4484695 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term226 A K k t x i) = (term76 A K k t x i).
Proof. exact (eq_refl (term226 A K k t x i)). Qed.
Lemma lem4484696 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term313 A K s k t x i) = (term314 A K s k t x i).
Proof. exact (MK_COMB (@lem4484694 A K k s x i) (@lem4484695 A K k t x i)). Qed.
Lemma lem4484697 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term315 A K s k t x) = (term316 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4484696 A K s k t x i)). Qed.
Lemma lem4484698 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484699 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term306 A K s k t x) = (term317 A K s k t x).
Proof. exact (MK_COMB (@lem4484698 K) (@lem4484697 A K s k t x)). Qed.
Lemma lem4484700 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : ((term305 A K s k t x) = (term306 A K s k t x)) = ((term82 A K s k t x) = (term317 A K s k t x)).
Proof. exact (MK_COMB (@lem4484691 A K s k t x) (@lem4484699 A K s k t x)). Qed.
Lemma lem4484701 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term317 A K s k t x).
Proof. exact (EQ_MP (@lem4484700 A K s k t x) (@lem4484678 A K s k t x)). Qed.
Lemma lem4484703 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4484704 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (@lem4484703 A P Q). Qed.
Lemma lem4484705 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term318 A K s k t x i) = (term319 A K s k t x i).
Proof. exact (@lem4484704 A (term74 A K k s x i) (term74 A K k t x i)). Qed.
Lemma lem4484706 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term219 A K k s x i x')). Qed.
Lemma lem4484707 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term320 A K k s x i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4484706 A K k s x i x')). Qed.
Lemma lem4484708 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484709 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term321 A K k s x i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4484708 A) (@lem4484707 A K k s x i)). Qed.
Lemma lem4484710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484711 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term322 A K k s x i) = (term312 A K k s x i).
Proof. exact (MK_COMB (@lem4484710) (@lem4484709 A K k s x i)). Qed.
Lemma lem4484712 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term219 A K k t x i x')). Qed.
Lemma lem4484713 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term320 A K k t x i) = (term74 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484712 A K k t x i x')). Qed.
Lemma lem4484714 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484715 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term321 A K k t x i) = (term76 A K k t x i).
Proof. exact (MK_COMB (@lem4484714 A) (@lem4484713 A K k t x i)). Qed.
Lemma lem4484716 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term318 A K s k t x i) = (term314 A K s k t x i).
Proof. exact (MK_COMB (@lem4484711 A K k s x i) (@lem4484715 A K k t x i)). Qed.
Lemma lem4484717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484718 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term323 A K s k t x i) = (term324 A K s k t x i).
Proof. exact (MK_COMB (@lem4484717) (@lem4484716 A K s k t x i)). Qed.
Lemma lem4484719 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term219 A K k s x i x')). Qed.
Lemma lem4484720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484721 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term325 A K k s x i x') = (term326 A K k s x i x').
Proof. exact (MK_COMB (@lem4484720) (@lem4484719 A K k s x i x')). Qed.
Lemma lem4484722 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term219 A K k t x i x')). Qed.
Lemma lem4484723 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term327 A K s k t x i x') = (term328 A K s k t x i x').
Proof. exact (MK_COMB (@lem4484721 A K k s x i x') (@lem4484722 A K k t x i x')). Qed.
Lemma lem4484724 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term329 A K s k t x i) = (term330 A K s k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484723 A K s k t x i x')). Qed.
Lemma lem4484725 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484726 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term319 A K s k t x i) = (term331 A K s k t x i).
Proof. exact (MK_COMB (@lem4484725 A) (@lem4484724 A K s k t x i)). Qed.
Lemma lem4484727 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : ((term318 A K s k t x i) = (term319 A K s k t x i)) = ((term314 A K s k t x i) = (term331 A K s k t x i)).
Proof. exact (MK_COMB (@lem4484718 A K s k t x i) (@lem4484726 A K s k t x i)). Qed.
Lemma lem4484728 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term314 A K s k t x i) = (term331 A K s k t x i).
Proof. exact (EQ_MP (@lem4484727 A K s k t x i) (@lem4484705 A K s k t x i)). Qed.
Lemma lem4484729 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term316 A K s k t x) = (term332 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4484728 A K s k t x i)). Qed.
Lemma lem4484730 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484731 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term317 A K s k t x) = (term333 A K s k t x).
Proof. exact (MK_COMB (@lem4484730 K) (@lem4484729 A K s k t x)). Qed.
Lemma lem4484732 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term333 A K s k t x).
Proof. exact (TRANS (@lem4484701 A K s k t x) (@lem4484731 A K s k t x)). Qed.
Lemma lem4484733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484734 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term265 A K s k t x) = (term334 A K s k t x).
Proof. exact (MK_COMB (@lem4484733) (@lem4484732 A K s k t x)). Qed.
Lemma lem4484735 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4484736 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term267 A K k s t x) = (term335 A K k s t x).
Proof. exact (MK_COMB (@lem4484734 A K s k t x) (@lem4484735 A K k s t x)). Qed.
Lemma lem4484738 {A : Type'} (P : A -> Prop) (Q : Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4484739 {K : Type'} (P : K -> Prop) (Q : Prop) : (term336 K P Q) = (term337 K P Q).
Proof. exact (@lem4484738 K P Q). Qed.
Lemma lem4484740 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term338 A K k s t x) = (term339 A K k s t x).
Proof. exact (@lem4484739 K (term332 A K s k t x) (term260 A K k s t x)). Qed.
Lemma lem4484741 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term340 A K s k t x i) = (term331 A K s k t x i).
Proof. exact (eq_refl (term340 A K s k t x i)). Qed.
Lemma lem4484742 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term341 A K s k t x) = (term332 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4484741 A K s k t x i)). Qed.
Lemma lem4484743 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484744 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term342 A K s k t x) = (term333 A K s k t x).
Proof. exact (MK_COMB (@lem4484743 K) (@lem4484742 A K s k t x)). Qed.
Lemma lem4484745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484746 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term343 A K s k t x) = (term334 A K s k t x).
Proof. exact (MK_COMB (@lem4484745) (@lem4484744 A K s k t x)). Qed.
Lemma lem4484747 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4484748 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term338 A K k s t x) = (term335 A K k s t x).
Proof. exact (MK_COMB (@lem4484746 A K s k t x) (@lem4484747 A K k s t x)). Qed.
Lemma lem4484749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484750 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term344 A K k s t x) = (term345 A K k s t x).
Proof. exact (MK_COMB (@lem4484749) (@lem4484748 A K k s t x)). Qed.
Lemma lem4484751 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term340 A K s k t x i) = (term331 A K s k t x i).
Proof. exact (eq_refl (term340 A K s k t x i)). Qed.
Lemma lem4484752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484753 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term346 A K s k t x i) = (term347 A K s k t x i).
Proof. exact (MK_COMB (@lem4484752) (@lem4484751 A K s k t x i)). Qed.
Lemma lem4484754 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4484755 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term348 A K i k s t x) = (term349 A K i k s t x).
Proof. exact (MK_COMB (@lem4484753 A K s k t x i) (@lem4484754 A K k s t x)). Qed.
Lemma lem4484756 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term350 A K k s t x) = (term351 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484755 A K i k s t x)). Qed.
Lemma lem4484757 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484758 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term339 A K k s t x) = (term352 A K k s t x).
Proof. exact (MK_COMB (@lem4484757 K) (@lem4484756 A K k s t x)). Qed.
Lemma lem4484759 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term338 A K k s t x) = (term339 A K k s t x)) = ((term335 A K k s t x) = (term352 A K k s t x)).
Proof. exact (MK_COMB (@lem4484750 A K k s t x) (@lem4484758 A K k s t x)). Qed.
Lemma lem4484760 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term335 A K k s t x) = (term352 A K k s t x).
Proof. exact (EQ_MP (@lem4484759 A K k s t x) (@lem4484740 A K k s t x)). Qed.
Lemma lem4484762 {A : Type'} (P : A -> Prop) (Q : Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4484763 {A : Type'} (P : A -> Prop) (Q : Prop) : (term336 A P Q) = (term337 A P Q).
Proof. exact (@lem4484762 A P Q). Qed.
Lemma lem4484764 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term353 A K i k s t x) = (term354 A K i k s t x).
Proof. exact (@lem4484763 A (term330 A K s k t x i) (term260 A K k s t x)). Qed.
Lemma lem4484765 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term355 A K s k t x i x') = (term328 A K s k t x i x').
Proof. exact (eq_refl (term355 A K s k t x i x')). Qed.
Lemma lem4484766 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term356 A K s k t x i) = (term330 A K s k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484765 A K s k t x i x')). Qed.
Lemma lem4484767 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484768 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term357 A K s k t x i) = (term331 A K s k t x i).
Proof. exact (MK_COMB (@lem4484767 A) (@lem4484766 A K s k t x i)). Qed.
Lemma lem4484769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484770 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term358 A K s k t x i) = (term347 A K s k t x i).
Proof. exact (MK_COMB (@lem4484769) (@lem4484768 A K s k t x i)). Qed.
Lemma lem4484771 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4484772 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term353 A K i k s t x) = (term349 A K i k s t x).
Proof. exact (MK_COMB (@lem4484770 A K s k t x i) (@lem4484771 A K k s t x)). Qed.
Lemma lem4484773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484774 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term359 A K i k s t x) = (term360 A K i k s t x).
Proof. exact (MK_COMB (@lem4484773) (@lem4484772 A K i k s t x)). Qed.
Lemma lem4484775 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term355 A K s k t x i x') = (term328 A K s k t x i x').
Proof. exact (eq_refl (term355 A K s k t x i x')). Qed.
Lemma lem4484776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4484777 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term361 A K s k t x i x') = (term362 A K s k t x i x').
Proof. exact (MK_COMB (@lem4484776) (@lem4484775 A K s k t x i x')). Qed.
Lemma lem4484778 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4484779 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term363 A K i x k s t x') = (term364 A K i x k s t x').
Proof. exact (MK_COMB (@lem4484777 A K s k t x' i x) (@lem4484778 A K k s t x')). Qed.
Lemma lem4484780 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term365 A K i k s t x) = (term366 A K i k s t x).
Proof. exact (fun_ext (fun x' : A => @lem4484779 A K i x' k s t x)). Qed.
Lemma lem4484781 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484782 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term354 A K i k s t x) = (term367 A K i k s t x).
Proof. exact (MK_COMB (@lem4484781 A) (@lem4484780 A K i k s t x)). Qed.
Lemma lem4484783 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term353 A K i k s t x) = (term354 A K i k s t x)) = ((term349 A K i k s t x) = (term367 A K i k s t x)).
Proof. exact (MK_COMB (@lem4484774 A K i k s t x) (@lem4484782 A K i k s t x)). Qed.
Lemma lem4484784 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term349 A K i k s t x) = (term367 A K i k s t x).
Proof. exact (EQ_MP (@lem4484783 A K i k s t x) (@lem4484764 A K i k s t x)). Qed.
Lemma lem4484785 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term351 A K k s t x) = (term368 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484784 A K i k s t x)). Qed.
Lemma lem4484786 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484787 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term352 A K k s t x) = (term369 A K k s t x).
Proof. exact (MK_COMB (@lem4484786 K) (@lem4484785 A K k s t x)). Qed.
Lemma lem4484788 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term335 A K k s t x) = (term369 A K k s t x).
Proof. exact (TRANS (@lem4484760 A K k s t x) (@lem4484787 A K k s t x)). Qed.
Lemma lem4484789 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term267 A K k s t x) = (term369 A K k s t x).
Proof. exact (TRANS (@lem4484736 A K k s t x) (@lem4484788 A K k s t x)). Qed.
Lemma lem4484790 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term287 A K k s t) = (term370 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484789 A K k s t x)). Qed.
Lemma lem4484791 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484792 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term298 A K k s t) = (term371 A K k s t).
Proof. exact (MK_COMB (@lem4484791 A K) (@lem4484790 A K k s t)). Qed.
Lemma lem4484793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484794 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term300 A K k s t) = (term372 A K k s t).
Proof. exact (MK_COMB (@lem4484793) (@lem4484792 A K k s t)). Qed.
Lemma lem4484796 {A : Type'} (P : Prop) (Q : A -> Prop) : (term373 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4484797 {K : Type'} (P : Prop) (Q : K -> Prop) : (term373 K P Q) = (term374 K P Q).
Proof. exact (@lem4484796 K P Q). Qed.
Lemma lem4484798 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term375 A K k s t x) = (term376 A K k s t x).
Proof. exact (@lem4484797 K (term234 A K s k t x) (term145 A K k s t x)). Qed.
Lemma lem4484799 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term256 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (eq_refl (term256 A K k s t x i)). Qed.
Lemma lem4484800 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term377 A K k s t x) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484799 A K k s t x i)). Qed.
Lemma lem4484801 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484802 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term378 A K k s t x) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4484801 K) (@lem4484800 A K k s t x)). Qed.
Lemma lem4484803 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4484804 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term375 A K k s t x) = (term264 A K k s t x).
Proof. exact (MK_COMB (@lem4484803 A K s k t x) (@lem4484802 A K k s t x)). Qed.
Lemma lem4484805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484806 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term379 A K k s t x) = (term380 A K k s t x).
Proof. exact (MK_COMB (@lem4484805) (@lem4484804 A K k s t x)). Qed.
Lemma lem4484807 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term256 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (eq_refl (term256 A K k s t x i)). Qed.
Lemma lem4484808 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4484809 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term381 A K k s t x i) = (term382 A K k s t x i).
Proof. exact (MK_COMB (@lem4484808 A K s k t x) (@lem4484807 A K k s t x i)). Qed.
Lemma lem4484810 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term383 A K k s t x) = (term384 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484809 A K k s t x i)). Qed.
Lemma lem4484811 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484812 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term376 A K k s t x) = (term385 A K k s t x).
Proof. exact (MK_COMB (@lem4484811 K) (@lem4484810 A K k s t x)). Qed.
Lemma lem4484813 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term375 A K k s t x) = (term376 A K k s t x)) = ((term264 A K k s t x) = (term385 A K k s t x)).
Proof. exact (MK_COMB (@lem4484806 A K k s t x) (@lem4484812 A K k s t x)). Qed.
Lemma lem4484814 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term264 A K k s t x) = (term385 A K k s t x).
Proof. exact (EQ_MP (@lem4484813 A K k s t x) (@lem4484798 A K k s t x)). Qed.
Lemma lem4484816 {A : Type'} (P : Prop) (Q : A -> Prop) : (term373 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4484817 {A : Type'} (P : Prop) (Q : A -> Prop) : (term373 A P Q) = (term374 A P Q).
Proof. exact (@lem4484816 A P Q). Qed.
Lemma lem4484818 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term386 A K k s t x i) = (term387 A K k s t x i).
Proof. exact (@lem4484817 A (term234 A K s k t x) (term141 A K k s t x i)). Qed.
Lemma lem4484819 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term249 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term249 A K k s t x i x')). Qed.
Lemma lem4484820 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term388 A K k s t x i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484819 A K k s t x i x')). Qed.
Lemma lem4484821 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484822 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term389 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4484821 A) (@lem4484820 A K k s t x i)). Qed.
Lemma lem4484823 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4484824 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term386 A K k s t x i) = (term382 A K k s t x i).
Proof. exact (MK_COMB (@lem4484823 A K s k t x) (@lem4484822 A K k s t x i)). Qed.
Lemma lem4484825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484826 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term390 A K k s t x i) = (term391 A K k s t x i).
Proof. exact (MK_COMB (@lem4484825) (@lem4484824 A K k s t x i)). Qed.
Lemma lem4484827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term249 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term249 A K k s t x i x')). Qed.
Lemma lem4484828 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4484829 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term392 A K k s t x i x') = (term393 A K k s t x i x').
Proof. exact (MK_COMB (@lem4484828 A K s k t x) (@lem4484827 A K k s t x i x')). Qed.
Lemma lem4484830 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term394 A K k s t x i) = (term395 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484829 A K k s t x i x')). Qed.
Lemma lem4484831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484832 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term387 A K k s t x i) = (term396 A K k s t x i).
Proof. exact (MK_COMB (@lem4484831 A) (@lem4484830 A K k s t x i)). Qed.
Lemma lem4484833 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : ((term386 A K k s t x i) = (term387 A K k s t x i)) = ((term382 A K k s t x i) = (term396 A K k s t x i)).
Proof. exact (MK_COMB (@lem4484826 A K k s t x i) (@lem4484832 A K k s t x i)). Qed.
Lemma lem4484834 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term382 A K k s t x i) = (term396 A K k s t x i).
Proof. exact (EQ_MP (@lem4484833 A K k s t x i) (@lem4484818 A K k s t x i)). Qed.
Lemma lem4484835 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term384 A K k s t x) = (term397 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484834 A K k s t x i)). Qed.
Lemma lem4484836 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484837 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term385 A K k s t x) = (term398 A K k s t x).
Proof. exact (MK_COMB (@lem4484836 K) (@lem4484835 A K k s t x)). Qed.
Lemma lem4484838 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term264 A K k s t x) = (term398 A K k s t x).
Proof. exact (TRANS (@lem4484814 A K k s t x) (@lem4484837 A K k s t x)). Qed.
Lemma lem4484839 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term288 A K k s t) = (term399 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484838 A K k s t x)). Qed.
Lemma lem4484840 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484841 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term303 A K k s t) = (term400 A K k s t).
Proof. exact (MK_COMB (@lem4484840 A K) (@lem4484839 A K k s t)). Qed.
Lemma lem4484842 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term304 A K k s t) = (term401 A K k s t).
Proof. exact (MK_COMB (@lem4484794 A K k s t) (@lem4484841 A K k s t)). Qed.
Lemma lem4484844 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4484845 {A K : Type'} (P : type1223 A K) (Q : type1223 A K) : (term284 A K P Q) = (term283 A K P Q).
Proof. exact (@lem4484844 (prod K A) P Q). Qed.
Lemma lem4484846 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term402 A K k s t) = (term403 A K k s t).
Proof. exact (@lem4484845 A K (term370 A K k s t) (term399 A K k s t)). Qed.
Lemma lem4484847 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term404 A K k s t x) = (term369 A K k s t x).
Proof. exact (eq_refl (term404 A K k s t x)). Qed.
Lemma lem4484848 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term405 A K k s t) = (term370 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484847 A K k s t x)). Qed.
Lemma lem4484849 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484850 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term406 A K k s t) = (term371 A K k s t).
Proof. exact (MK_COMB (@lem4484849 A K) (@lem4484848 A K k s t)). Qed.
Lemma lem4484851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484852 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term407 A K k s t) = (term372 A K k s t).
Proof. exact (MK_COMB (@lem4484851) (@lem4484850 A K k s t)). Qed.
Lemma lem4484853 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term408 A K k s t x) = (term398 A K k s t x).
Proof. exact (eq_refl (term408 A K k s t x)). Qed.
Lemma lem4484854 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term409 A K k s t) = (term399 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484853 A K k s t x)). Qed.
Lemma lem4484855 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484856 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term410 A K k s t) = (term400 A K k s t).
Proof. exact (MK_COMB (@lem4484855 A K) (@lem4484854 A K k s t)). Qed.
Lemma lem4484857 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term402 A K k s t) = (term401 A K k s t).
Proof. exact (MK_COMB (@lem4484852 A K k s t) (@lem4484856 A K k s t)). Qed.
Lemma lem4484858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484859 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term411 A K k s t) = (term412 A K k s t).
Proof. exact (MK_COMB (@lem4484858) (@lem4484857 A K k s t)). Qed.
Lemma lem4484860 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term404 A K k s t x) = (term369 A K k s t x).
Proof. exact (eq_refl (term404 A K k s t x)). Qed.
Lemma lem4484861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484862 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term413 A K k s t x) = (term414 A K k s t x).
Proof. exact (MK_COMB (@lem4484861) (@lem4484860 A K k s t x)). Qed.
Lemma lem4484863 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term408 A K k s t x) = (term398 A K k s t x).
Proof. exact (eq_refl (term408 A K k s t x)). Qed.
Lemma lem4484864 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term415 A K k s t x) = (term416 A K k s t x).
Proof. exact (MK_COMB (@lem4484862 A K k s t x) (@lem4484863 A K k s t x)). Qed.
Lemma lem4484865 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term417 A K k s t) = (term418 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484864 A K k s t x)). Qed.
Lemma lem4484866 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484867 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term403 A K k s t) = (term419 A K k s t).
Proof. exact (MK_COMB (@lem4484866 A K) (@lem4484865 A K k s t)). Qed.
Lemma lem4484868 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term402 A K k s t) = (term403 A K k s t)) = ((term401 A K k s t) = (term419 A K k s t)).
Proof. exact (MK_COMB (@lem4484859 A K k s t) (@lem4484867 A K k s t)). Qed.
Lemma lem4484869 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term401 A K k s t) = (term419 A K k s t).
Proof. exact (EQ_MP (@lem4484868 A K k s t) (@lem4484846 A K k s t)). Qed.
Lemma lem4484871 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4484872 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term282 K P Q) = (term281 K P Q).
Proof. exact (@lem4484871 K P Q). Qed.
Lemma lem4484873 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term420 A K k s t x) = (term421 A K k s t x).
Proof. exact (@lem4484872 K (term368 A K k s t x) (term397 A K k s t x)). Qed.
Lemma lem4484874 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term422 A K k s t x i) = (term367 A K i k s t x).
Proof. exact (eq_refl (term422 A K k s t x i)). Qed.
Lemma lem4484875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term423 A K k s t x) = (term368 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484874 A K i k s t x)). Qed.
Lemma lem4484876 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484877 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term424 A K k s t x) = (term369 A K k s t x).
Proof. exact (MK_COMB (@lem4484876 K) (@lem4484875 A K k s t x)). Qed.
Lemma lem4484878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484879 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term425 A K k s t x) = (term414 A K k s t x).
Proof. exact (MK_COMB (@lem4484878) (@lem4484877 A K k s t x)). Qed.
Lemma lem4484880 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term426 A K k s t x i) = (term396 A K k s t x i).
Proof. exact (eq_refl (term426 A K k s t x i)). Qed.
Lemma lem4484881 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term427 A K k s t x) = (term397 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484880 A K k s t x i)). Qed.
Lemma lem4484882 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484883 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term428 A K k s t x) = (term398 A K k s t x).
Proof. exact (MK_COMB (@lem4484882 K) (@lem4484881 A K k s t x)). Qed.
Lemma lem4484884 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term420 A K k s t x) = (term416 A K k s t x).
Proof. exact (MK_COMB (@lem4484879 A K k s t x) (@lem4484883 A K k s t x)). Qed.
Lemma lem4484885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484886 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term429 A K k s t x) = (term430 A K k s t x).
Proof. exact (MK_COMB (@lem4484885) (@lem4484884 A K k s t x)). Qed.
Lemma lem4484887 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term422 A K k s t x i) = (term367 A K i k s t x).
Proof. exact (eq_refl (term422 A K k s t x i)). Qed.
Lemma lem4484888 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484889 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term431 A K k s t x i) = (term432 A K i k s t x).
Proof. exact (MK_COMB (@lem4484888) (@lem4484887 A K i k s t x)). Qed.
Lemma lem4484890 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term426 A K k s t x i) = (term396 A K k s t x i).
Proof. exact (eq_refl (term426 A K k s t x i)). Qed.
Lemma lem4484891 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term433 A K k s t x i) = (term434 A K k s t x i).
Proof. exact (MK_COMB (@lem4484889 A K i k s t x) (@lem4484890 A K k s t x i)). Qed.
Lemma lem4484892 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term435 A K k s t x) = (term436 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484891 A K k s t x i)). Qed.
Lemma lem4484893 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484894 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term421 A K k s t x) = (term437 A K k s t x).
Proof. exact (MK_COMB (@lem4484893 K) (@lem4484892 A K k s t x)). Qed.
Lemma lem4484895 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term420 A K k s t x) = (term421 A K k s t x)) = ((term416 A K k s t x) = (term437 A K k s t x)).
Proof. exact (MK_COMB (@lem4484886 A K k s t x) (@lem4484894 A K k s t x)). Qed.
Lemma lem4484896 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term416 A K k s t x) = (term437 A K k s t x).
Proof. exact (EQ_MP (@lem4484895 A K k s t x) (@lem4484873 A K k s t x)). Qed.
Lemma lem4484898 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4484899 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (@lem4484898 A P Q). Qed.
Lemma lem4484900 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term438 A K k s t x i) = (term439 A K k s t x i).
Proof. exact (@lem4484899 A (term366 A K i k s t x) (term395 A K k s t x i)). Qed.
Lemma lem4484901 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term440 A K i k s t x' x) = (term364 A K i x k s t x').
Proof. exact (eq_refl (term440 A K i k s t x' x)). Qed.
Lemma lem4484902 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term441 A K i k s t x) = (term366 A K i k s t x).
Proof. exact (fun_ext (fun x' : A => @lem4484901 A K i x' k s t x)). Qed.
Lemma lem4484903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484904 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term442 A K i k s t x) = (term367 A K i k s t x).
Proof. exact (MK_COMB (@lem4484903 A) (@lem4484902 A K i k s t x)). Qed.
Lemma lem4484905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484906 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term443 A K i k s t x) = (term432 A K i k s t x).
Proof. exact (MK_COMB (@lem4484905) (@lem4484904 A K i k s t x)). Qed.
Lemma lem4484907 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term444 A K k s t x i x') = (term393 A K k s t x i x').
Proof. exact (eq_refl (term444 A K k s t x i x')). Qed.
Lemma lem4484908 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term445 A K k s t x i) = (term395 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484907 A K k s t x i x')). Qed.
Lemma lem4484909 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484910 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term446 A K k s t x i) = (term396 A K k s t x i).
Proof. exact (MK_COMB (@lem4484909 A) (@lem4484908 A K k s t x i)). Qed.
Lemma lem4484911 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term438 A K k s t x i) = (term434 A K k s t x i).
Proof. exact (MK_COMB (@lem4484906 A K i k s t x) (@lem4484910 A K k s t x i)). Qed.
Lemma lem4484912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4484913 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term447 A K k s t x i) = (term448 A K k s t x i).
Proof. exact (MK_COMB (@lem4484912) (@lem4484911 A K k s t x i)). Qed.
Lemma lem4484914 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term440 A K i k s t x' x) = (term364 A K i x k s t x').
Proof. exact (eq_refl (term440 A K i k s t x' x)). Qed.
Lemma lem4484915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4484916 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term449 A K i k s t x' x) = (term450 A K i x k s t x').
Proof. exact (MK_COMB (@lem4484915) (@lem4484914 A K i x k s t x')). Qed.
Lemma lem4484917 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term444 A K k s t x i x') = (term393 A K k s t x i x').
Proof. exact (eq_refl (term444 A K k s t x i x')). Qed.
Lemma lem4484918 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term451 A K k s t x i x') = (term452 A K k s t x i x').
Proof. exact (MK_COMB (@lem4484916 A K i x' k s t x) (@lem4484917 A K k s t x i x')). Qed.
Lemma lem4484919 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term453 A K k s t x i) = (term454 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4484918 A K k s t x i x')). Qed.
Lemma lem4484920 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4484921 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term439 A K k s t x i) = (term455 A K k s t x i).
Proof. exact (MK_COMB (@lem4484920 A) (@lem4484919 A K k s t x i)). Qed.
Lemma lem4484922 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : ((term438 A K k s t x i) = (term439 A K k s t x i)) = ((term434 A K k s t x i) = (term455 A K k s t x i)).
Proof. exact (MK_COMB (@lem4484913 A K k s t x i) (@lem4484921 A K k s t x i)). Qed.
Lemma lem4484923 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term434 A K k s t x i) = (term455 A K k s t x i).
Proof. exact (EQ_MP (@lem4484922 A K k s t x i) (@lem4484900 A K k s t x i)). Qed.
Lemma lem4484924 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term436 A K k s t x) = (term456 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4484923 A K k s t x i)). Qed.
Lemma lem4484925 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4484926 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term437 A K k s t x) = (term457 A K k s t x).
Proof. exact (MK_COMB (@lem4484925 K) (@lem4484924 A K k s t x)). Qed.
Lemma lem4484927 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term416 A K k s t x) = (term457 A K k s t x).
Proof. exact (TRANS (@lem4484896 A K k s t x) (@lem4484926 A K k s t x)). Qed.
Lemma lem4484928 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term418 A K k s t) = (term458 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4484927 A K k s t x)). Qed.
Lemma lem4484929 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4484930 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term419 A K k s t) = (term459 A K k s t).
Proof. exact (MK_COMB (@lem4484929 A K) (@lem4484928 A K k s t)). Qed.
Lemma lem4484931 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term401 A K k s t) = (term459 A K k s t).
Proof. exact (TRANS (@lem4484869 A K k s t) (@lem4484930 A K k s t)). Qed.
Lemma lem4484932 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term304 A K k s t) = (term459 A K k s t).
Proof. exact (TRANS (@lem4484842 A K k s t) (@lem4484931 A K k s t)). Qed.
Lemma lem4484933 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term280 A K k s t) = (term459 A K k s t).
Proof. exact (TRANS (@lem4484266 A K k s t) (@lem4484932 A K k s t)). Qed.
Lemma lem4484934 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term459 A K k s t).
Proof. exact (TRANS (@lem4484239 A K k s t) (@lem4484933 A K k s t)). Qed.
Lemma lem4484935 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term459 A K k s t.
Proof. exact (EQ_MP (@lem4484934 A K k s t) (@lem4484053 A K k s t h1)). Qed.
Lemma lem4486751 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term457 A K k s t x) : term457 A K k s t x.
Proof. exact (h1). Qed.
Lemma lem4486752 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (h1 : term455 A K k s t x i) : term455 A K k s t x i.
Proof. exact (h1). Qed.
Lemma lem4486753 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term452 A K k s t x i x') : term452 A K k s t x i x'.
Proof. exact (h1). Qed.
Lemma lem4487066 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term139 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term139 A K k s t x i x')). Qed.
Lemma lem4487099 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (eq_refl (term213 A K k t x i x')). Qed.
Lemma lem4487100 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term222 A K k t x i) = (term222 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4487099 A K k t x i x')). Qed.
Lemma lem4487101 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4487102 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term223 A K k t x i) = (term223 A K k t x i).
Proof. exact (MK_COMB (@lem4487101 A) (@lem4487100 A K k t x i)). Qed.
Lemma lem4487103 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term229 A K k t x) = (term229 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4487102 A K k t x i)). Qed.
Lemma lem4487104 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4487105 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term230 A K k t x) = (term230 A K k t x).
Proof. exact (MK_COMB (@lem4487104 K) (@lem4487103 A K k t x)). Qed.
Lemma lem4487138 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (eq_refl (term213 A K k s x i x')). Qed.
Lemma lem4487139 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term222 A K k s x i) = (term222 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4487138 A K k s x i x')). Qed.
Lemma lem4487140 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4487141 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term223 A K k s x i) = (term223 A K k s x i).
Proof. exact (MK_COMB (@lem4487140 A) (@lem4487139 A K k s x i)). Qed.
Lemma lem4487142 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term229 A K k s x) = (term229 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4487141 A K k s x i)). Qed.
Lemma lem4487143 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4487144 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term230 A K k s x) = (term230 A K k s x).
Proof. exact (MK_COMB (@lem4487143 K) (@lem4487142 A K k s x)). Qed.
Lemma lem4487145 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4487146 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term232 A K k s x) = (term232 A K k s x).
Proof. exact (MK_COMB (@lem4487145) (@lem4487144 A K k s x)). Qed.
Lemma lem4487147 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term234 A K s k t x) = (term234 A K s k t x).
Proof. exact (MK_COMB (@lem4487146 A K k s x) (@lem4487105 A K k t x)). Qed.
Lemma lem4487148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4487149 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (MK_COMB (@lem4487148) (@lem4487147 A K s k t x)). Qed.
Lemma lem4487150 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term393 A K k s t x i x') = (term393 A K k s t x i x').
Proof. exact (MK_COMB (@lem4487149 A K s k t x) (@lem4487066 A K k s t x i x')). Qed.
Lemma lem4487195 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term245 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (eq_refl (term245 A K k s t x i x')). Qed.
Lemma lem4487196 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term252 A K k s t x i) = (term252 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4487195 A K k s t x i x')). Qed.
Lemma lem4487197 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4487198 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term253 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (MK_COMB (@lem4487197 A) (@lem4487196 A K k s t x i)). Qed.
Lemma lem4487199 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term259 A K k s t x) = (term259 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4487198 A K k s t x i)). Qed.
Lemma lem4487200 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4487201 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (MK_COMB (@lem4487200 K) (@lem4487199 A K k s t x)). Qed.
Lemma lem4487260 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term362 A K s k t x i x') = (term362 A K s k t x i x').
Proof. exact (eq_refl (term362 A K s k t x i x')). Qed.
Lemma lem4487261 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term364 A K i x' k s t x) = (term364 A K i x' k s t x).
Proof. exact (MK_COMB (@lem4487260 A K s k t x i x') (@lem4487201 A K k s t x)). Qed.
Lemma lem4487262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4487263 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term450 A K i x' k s t x) = (term450 A K i x' k s t x).
Proof. exact (MK_COMB (@lem4487262) (@lem4487261 A K i x' k s t x)). Qed.
Lemma lem4487264 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term452 A K k s t x i x') = (term452 A K k s t x i x').
Proof. exact (MK_COMB (@lem4487263 A K i x' k s t x) (@lem4487150 A K k s t x i x')). Qed.
Lemma lem4487265 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term452 A K k s t x i x') : term452 A K k s t x i x'.
Proof. exact (EQ_MP (@lem4487264 A K k s t x i x') (@lem4486753 A K k s t x i x' h1)). Qed.
Lemma lem4487272 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term364 A K i x' k s t x.
Proof. exact (h1). Qed.
Lemma lem4487273 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term393 A K k s t x i x'.
Proof. exact (h1). Qed.
Lemma lem4487274 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term260 A K k s t x.
Proof. exact (proj2 (@lem4487272 A K i x' k s t x h1)). Qed.
Lemma lem4487275 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term328 A K s k t x i x'.
Proof. exact (proj1 (@lem4487272 A K i x' k s t x h1)). Qed.
Lemma lem4487276 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term72 A K k s x i x'.
Proof. exact (h1). Qed.
Lemma lem4487277 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term72 A K k t x i x'.
Proof. exact (h1). Qed.
Lemma lem4487279 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term56 A K k x' s i.
Proof. exact (proj1 (@lem4487276 A K k s x i x' h1)). Qed.
Lemma lem4487283 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term56 A K k x' t i.
Proof. exact (proj1 (@lem4487277 A K k t x i x' h1)). Qed.
Lemma lem4487286 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term139 A K k s t x i x'.
Proof. exact (proj2 (@lem4487273 A K k s t x i x' h1)). Qed.
Lemma lem4487287 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term234 A K s k t x.
Proof. exact (proj1 (@lem4487273 A K k s t x i x' h1)). Qed.
Lemma lem4487289 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term99 A K k s x' t i.
Proof. exact (proj1 (@lem4487286 A K k s t x i x' h1)). Qed.
Lemma lem4487290 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term96 A K s x' t i.
Proof. exact (proj2 (@lem4487289 A K k s t x i x' h1)). Qed.
Lemma lem4487292 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term230 A K k t x.
Proof. exact (proj2 (@lem4487287 A K k s t x i x' h1)). Qed.
Lemma lem4487293 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term230 A K k s x.
Proof. exact (proj1 (@lem4487287 A K k s t x i x' h1)). Qed.
Lemma lem4487477 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4487494 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term240 A K k s x t i) = (term460 A K s k x t i).
Proof. exact (@lem19490 (term461 A K x s i) (term462 K i k) (term461 A K x t i)). Qed.
Lemma lem4487495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4487496 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term243 A K k s x t i) = (term463 A K s k x t i).
Proof. exact (MK_COMB (@lem4487495) (@lem4487494 A K s k x t i)). Qed.
Lemma lem4487497 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term245 A K k s t x i x') = (term464 A K s k t x i x').
Proof. exact (MK_COMB (@lem4487496 A K s k x' t i) (@lem4487477 A K x i x')). Qed.
Lemma lem4487504 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term464 A K s k t x i x') = (term465 A K s k t x i x').
Proof. exact (@lem19699 (term207 A K k x' s i) (term207 A K k x' t i) (term209 A K x i x')). Qed.
Lemma lem4487505 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term245 A K k s t x i x') = (term465 A K s k t x i x').
Proof. exact (TRANS (@lem4487497 A K s k t x i x') (@lem4487504 A K s k t x i x')). Qed.
Lemma lem4487506 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term252 A K k s t x i) = (term466 A K s k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4487505 A K s k t x i x')). Qed.
Lemma lem4487507 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4487508 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term253 A K k s t x i) = (term467 A K s k t x i).
Proof. exact (MK_COMB (@lem4487507 A) (@lem4487506 A K s k t x i)). Qed.
Lemma lem4487509 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term259 A K k s t x) = (term468 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4487508 A K s k t x i)). Qed.
Lemma lem4487510 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4487512 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term469 A K s k t x).
Proof. exact (MK_COMB (@lem4487510 K) (@lem4487509 A K s k t x)). Qed.
Lemma lem4487513 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term469 A K s k t x.
Proof. exact (EQ_MP (@lem4487512 A K s k t x) (@lem4487274 A K i x' k s t x h1)). Qed.
Lemma lem4487707 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4487724 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term240 A K k s x t i) = (term460 A K s k x t i).
Proof. exact (@lem19490 (term461 A K x s i) (term462 K i k) (term461 A K x t i)). Qed.
Lemma lem4487725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4487726 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term243 A K k s x t i) = (term463 A K s k x t i).
Proof. exact (MK_COMB (@lem4487725) (@lem4487724 A K s k x t i)). Qed.
Lemma lem4487727 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term245 A K k s t x i x') = (term464 A K s k t x i x').
Proof. exact (MK_COMB (@lem4487726 A K s k x' t i) (@lem4487707 A K x i x')). Qed.
Lemma lem4487734 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term464 A K s k t x i x') = (term465 A K s k t x i x').
Proof. exact (@lem19699 (term207 A K k x' s i) (term207 A K k x' t i) (term209 A K x i x')). Qed.
Lemma lem4487735 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term245 A K k s t x i x') = (term465 A K s k t x i x').
Proof. exact (TRANS (@lem4487727 A K s k t x i x') (@lem4487734 A K s k t x i x')). Qed.
Lemma lem4487736 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term252 A K k s t x i) = (term466 A K s k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4487735 A K s k t x i x')). Qed.
Lemma lem4487737 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4487738 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term253 A K k s t x i) = (term467 A K s k t x i).
Proof. exact (MK_COMB (@lem4487737 A) (@lem4487736 A K s k t x i)). Qed.
Lemma lem4487739 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term259 A K k s t x) = (term468 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4487738 A K s k t x i)). Qed.
Lemma lem4487740 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4487742 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term469 A K s k t x).
Proof. exact (MK_COMB (@lem4487740 K) (@lem4487739 A K s k t x)). Qed.
Lemma lem4487743 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term469 A K s k t x.
Proof. exact (EQ_MP (@lem4487742 A K s k t x) (@lem4487274 A K i x' k s t x h1)). Qed.
Lemma lem4487957 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (eq_refl (term213 A K k s x i x')). Qed.
Lemma lem4487958 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term222 A K k s x i) = (term222 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4487957 A K k s x i x')). Qed.
Lemma lem4487959 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4487960 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term223 A K k s x i) = (term223 A K k s x i).
Proof. exact (MK_COMB (@lem4487959 A) (@lem4487958 A K k s x i)). Qed.
Lemma lem4487961 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term229 A K k s x) = (term229 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4487960 A K k s x i)). Qed.
Lemma lem4487962 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4487964 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term230 A K k s x) = (term230 A K k s x).
Proof. exact (MK_COMB (@lem4487962 K) (@lem4487961 A K k s x)). Qed.
Lemma lem4487965 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term230 A K k s x.
Proof. exact (EQ_MP (@lem4487964 A K k s x) (@lem4487293 A K k s t x i x' h1)). Qed.
Lemma lem4487991 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) (h1 : term208 A K x' s i) : term208 A K x' s i.
Proof. exact (h1). Qed.
Lemma lem4488215 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (eq_refl (term213 A K k t x i x')). Qed.
Lemma lem4488216 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term222 A K k t x i) = (term222 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4488215 A K k t x i x')). Qed.
Lemma lem4488217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4488218 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term223 A K k t x i) = (term223 A K k t x i).
Proof. exact (MK_COMB (@lem4488217 A) (@lem4488216 A K k t x i)). Qed.
Lemma lem4488219 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term229 A K k t x) = (term229 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4488218 A K k t x i)). Qed.
Lemma lem4488220 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4488222 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term230 A K k t x) = (term230 A K k t x).
Proof. exact (MK_COMB (@lem4488220 K) (@lem4488219 A K k t x)). Qed.
Lemma lem4488223 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term230 A K k t x.
Proof. exact (EQ_MP (@lem4488222 A K k t x) (@lem4487292 A K k s t x i x' h1)). Qed.
Lemma lem4488227 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) (h1 : term208 A K x' t i) : term208 A K x' t i.
Proof. exact (h1). Qed.
Lemma lem4488300 {A K : Type'} (_52011 : K) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term470 A K s k t x _52011.
Proof. exact (@lem4487513 A K i x' k s t x h1 _52011). Qed.
Lemma lem4488301 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52011 : K) : (term470 A K s k t x _52011) = (term467 A K s k t x _52011).
Proof. exact (eq_refl (term470 A K s k t x _52011)). Qed.
Lemma lem4488302 {A K : Type'} (_52011 : K) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term467 A K s k t x _52011.
Proof. exact (EQ_MP (@lem4488301 A K s k t x _52011) (@lem4488300 A K _52011 i x' k s t x h1)). Qed.
Lemma lem4488303 {A K : Type'} (_52011 : K) (_52012 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term471 A K s k t x _52011 _52012.
Proof. exact (@lem4488302 A K _52011 i x' k s t x h1 _52012). Qed.
Lemma lem4488304 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52011 : K) (_52012 : A) : (term471 A K s k t x _52011 _52012) = (term465 A K s k t x _52011 _52012).
Proof. exact (eq_refl (term471 A K s k t x _52011 _52012)). Qed.
Lemma lem4488305 {A K : Type'} (_52011 : K) (_52012 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term465 A K s k t x _52011 _52012.
Proof. exact (EQ_MP (@lem4488304 A K s k t x _52011 _52012) (@lem4488303 A K _52011 _52012 i x' k s t x h1)). Qed.
Lemma lem4488378 {A K : Type'} (_52037 : K) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term470 A K s k t x _52037.
Proof. exact (@lem4487743 A K i x' k s t x h1 _52037). Qed.
Lemma lem4488379 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52037 : K) : (term470 A K s k t x _52037) = (term467 A K s k t x _52037).
Proof. exact (eq_refl (term470 A K s k t x _52037)). Qed.
Lemma lem4488380 {A K : Type'} (_52037 : K) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term467 A K s k t x _52037.
Proof. exact (EQ_MP (@lem4488379 A K s k t x _52037) (@lem4488378 A K _52037 i x' k s t x h1)). Qed.
Lemma lem4488381 {A K : Type'} (_52037 : K) (_52038 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term471 A K s k t x _52037 _52038.
Proof. exact (@lem4488380 A K _52037 i x' k s t x h1 _52038). Qed.
Lemma lem4488382 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52037 : K) (_52038 : A) : (term471 A K s k t x _52037 _52038) = (term465 A K s k t x _52037 _52038).
Proof. exact (eq_refl (term471 A K s k t x _52037 _52038)). Qed.
Lemma lem4488383 {A K : Type'} (_52037 : K) (_52038 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term465 A K s k t x _52037 _52038.
Proof. exact (EQ_MP (@lem4488382 A K s k t x _52037 _52038) (@lem4488381 A K _52037 _52038 i x' k s t x h1)). Qed.
Lemma lem4488456 {A K : Type'} (_52063 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term472 A K k s x _52063.
Proof. exact (@lem4487965 A K k s t x i x' h1 _52063). Qed.
Lemma lem4488457 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52063 : K) : (term472 A K k s x _52063) = (term223 A K k s x _52063).
Proof. exact (eq_refl (term472 A K k s x _52063)). Qed.
Lemma lem4488458 {A K : Type'} (_52063 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term223 A K k s x _52063.
Proof. exact (EQ_MP (@lem4488457 A K k s x _52063) (@lem4488456 A K _52063 k s t x i x' h1)). Qed.
Lemma lem4488459 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term473 A K k s x _52063 _52064.
Proof. exact (@lem4488458 A K _52063 k s t x i x' h1 _52064). Qed.
Lemma lem4488460 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52063 : K) (_52064 : A) : (term473 A K k s x _52063 _52064) = (term213 A K k s x _52063 _52064).
Proof. exact (eq_refl (term473 A K k s x _52063 _52064)). Qed.
Lemma lem4488461 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term213 A K k s x _52063 _52064.
Proof. exact (EQ_MP (@lem4488460 A K k s x _52063 _52064) (@lem4488459 A K _52063 _52064 k s t x i x' h1)). Qed.
Lemma lem4488546 {A K : Type'} (_52093 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term472 A K k t x _52093.
Proof. exact (@lem4488223 A K k s t x i x' h1 _52093). Qed.
Lemma lem4488547 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52093 : K) : (term472 A K k t x _52093) = (term223 A K k t x _52093).
Proof. exact (eq_refl (term472 A K k t x _52093)). Qed.
Lemma lem4488548 {A K : Type'} (_52093 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term223 A K k t x _52093.
Proof. exact (EQ_MP (@lem4488547 A K k t x _52093) (@lem4488546 A K _52093 k s t x i x' h1)). Qed.
Lemma lem4488549 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term473 A K k t x _52093 _52094.
Proof. exact (@lem4488548 A K _52093 k s t x i x' h1 _52094). Qed.
Lemma lem4488550 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52093 : K) (_52094 : A) : (term473 A K k t x _52093 _52094) = (term213 A K k t x _52093 _52094).
Proof. exact (eq_refl (term473 A K k t x _52093 _52094)). Qed.
Lemma lem4488551 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term213 A K k t x _52093 _52094.
Proof. exact (EQ_MP (@lem4488550 A K k t x _52093 _52094) (@lem4488549 A K _52093 _52094 k s t x i x' h1)). Qed.
Lemma lem4488553 {A K : Type'} (_52011 : K) (_52012 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term213 A K k s x _52011 _52012.
Proof. exact (proj1 (@lem4488305 A K _52011 _52012 i x' k s t x h1)). Qed.
Lemma lem4488560 {A K : Type'} (_52037 : K) (_52038 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term213 A K k t x _52037 _52038.
Proof. exact (proj2 (@lem4488383 A K _52037 _52038 i x' k s t x h1)). Qed.
Lemma lem4488611 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : x = (@pair K A i x').
Proof. exact (proj2 (@lem4487276 A K k s x i x' h1)). Qed.
Lemma lem4488626 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52011 : K) (_52012 : A) : (term213 A K k s x _52011 _52012) = (term474 A K k s x _52011 _52012).
Proof. exact (@lem4482980 (term462 K _52011 k) (term461 A K _52012 s _52011) (term209 A K x _52011 _52012)). Qed.
Lemma lem4488627 {A K : Type'} (_52011 : K) (_52012 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term474 A K k s x _52011 _52012.
Proof. exact (EQ_MP (@lem4488626 A K k s x _52011 _52012) (@lem4488553 A K _52011 _52012 i x' k s t x h1)). Qed.
Lemma lem4488707 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : x = (@pair K A i x').
Proof. exact (proj2 (@lem4487277 A K k t x i x' h1)). Qed.
Lemma lem4488734 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52037 : K) (_52038 : A) : (term213 A K k t x _52037 _52038) = (term474 A K k t x _52037 _52038).
Proof. exact (@lem4482980 (term462 K _52037 k) (term461 A K _52038 t _52037) (term209 A K x _52037 _52038)). Qed.
Lemma lem4488735 {A K : Type'} (_52037 : K) (_52038 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : term474 A K k t x _52037 _52038.
Proof. exact (EQ_MP (@lem4488734 A K k t x _52037 _52038) (@lem4488560 A K _52037 _52038 i x' k s t x h1)). Qed.
Lemma lem4488803 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : x = (@pair K A i x').
Proof. exact (proj2 (@lem4487286 A K k s t x i x' h1)). Qed.
Lemma lem4488816 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52063 : K) (_52064 : A) : (term213 A K k s x _52063 _52064) = (term474 A K k s x _52063 _52064).
Proof. exact (@lem4482980 (term462 K _52063 k) (term461 A K _52064 s _52063) (term209 A K x _52063 _52064)). Qed.
Lemma lem4488817 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term474 A K k s x _52063 _52064.
Proof. exact (EQ_MP (@lem4488816 A K k s x _52063 _52064) (@lem4488461 A K _52063 _52064 k s t x i x' h1)). Qed.
Lemma lem4488831 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) (h1 : term208 A K x' s i) : term208 A K x' s i.
Proof. exact (h1). Qed.
Lemma lem4488899 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : x = (@pair K A i x').
Proof. exact (proj2 (@lem4487286 A K k s t x i x' h1)). Qed.
Lemma lem4488924 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52093 : K) (_52094 : A) : (term213 A K k t x _52093 _52094) = (term474 A K k t x _52093 _52094).
Proof. exact (@lem4482980 (term462 K _52093 k) (term461 A K _52094 t _52093) (term209 A K x _52093 _52094)). Qed.
Lemma lem4488925 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term474 A K k t x _52093 _52094.
Proof. exact (EQ_MP (@lem4488924 A K k t x _52093 _52094) (@lem4488551 A K _52093 _52094 k s t x i x' h1)). Qed.
Lemma lem4488927 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) (h1 : term208 A K x' t i) : term208 A K x' t i.
Proof. exact (h1). Qed.
Lemma lem4489048 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52011 : K) (_52012 : A) : (term475 A K k s _52011 _52012) = (term475 A K k s _52011 _52012).
Proof. exact (eq_refl (term475 A K k s _52011 _52012)). Qed.
Lemma lem4489049 {A K : Type'} (_52011 : K) (_52012 : A) (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : (term476 A K k s _52011 _52012 x) = (term477 A K k s _52011 _52012 i x').
Proof. exact (MK_COMB (@lem4489048 A K k s _52011 _52012) (@lem4488611 A K k s x i x' h1)). Qed.
Lemma lem4489050 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term477 A K k s _52011 _52012 i x') = (term478 A K k s i x' _52011 _52012).
Proof. exact (eq_refl (term477 A K k s _52011 _52012 i x')). Qed.
Lemma lem4489051 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52011 : K) (_52012 : A) (x : prod K A) : (term479 A K k s _52011 _52012 x) = (term479 A K k s _52011 _52012 x).
Proof. exact (eq_refl (term479 A K k s _52011 _52012 x)). Qed.
Lemma lem4489052 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : ((term476 A K k s _52011 _52012 x) = (term477 A K k s _52011 _52012 i x')) = ((term476 A K k s _52011 _52012 x) = (term478 A K k s i x' _52011 _52012)).
Proof. exact (MK_COMB (@lem4489051 A K k s _52011 _52012 x) (@lem4489050 A K k s i x' _52011 _52012)). Qed.
Lemma lem4489053 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52011 : K) (_52012 : A) : (term476 A K k s _52011 _52012 x) = (term474 A K k s x _52011 _52012).
Proof. exact (eq_refl (term476 A K k s _52011 _52012 x)). Qed.
Lemma lem4489054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4489055 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52011 : K) (_52012 : A) : (term479 A K k s _52011 _52012 x) = (term480 A K k s x _52011 _52012).
Proof. exact (MK_COMB (@lem4489054) (@lem4489053 A K k s x _52011 _52012)). Qed.
Lemma lem4489056 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term478 A K k s i x' _52011 _52012) = (term478 A K k s i x' _52011 _52012).
Proof. exact (eq_refl (term478 A K k s i x' _52011 _52012)). Qed.
Lemma lem4489057 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : ((term476 A K k s _52011 _52012 x) = (term478 A K k s i x' _52011 _52012)) = ((term474 A K k s x _52011 _52012) = (term478 A K k s i x' _52011 _52012)).
Proof. exact (MK_COMB (@lem4489055 A K k s x _52011 _52012) (@lem4489056 A K k s i x' _52011 _52012)). Qed.
Lemma lem4489058 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : ((term476 A K k s _52011 _52012 x) = (term477 A K k s _52011 _52012 i x')) = ((term474 A K k s x _52011 _52012) = (term478 A K k s i x' _52011 _52012)).
Proof. exact (TRANS (@lem4489052 A K x k s i x' _52011 _52012) (@lem4489057 A K x k s i x' _52011 _52012)). Qed.
Lemma lem4489059 {A K : Type'} (_52011 : K) (_52012 : A) (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : (term474 A K k s x _52011 _52012) = (term478 A K k s i x' _52011 _52012).
Proof. exact (EQ_MP (@lem4489058 A K x k s i x' _52011 _52012) (@lem4489049 A K _52011 _52012 k s x i x' h1)). Qed.
Lemma lem4489060 {A K : Type'} (_52011 : K) (_52012 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k s x i x') (h2 : term364 A K i x' k s t x) : term478 A K k s i x' _52011 _52012.
Proof. exact (EQ_MP (@lem4489059 A K _52011 _52012 k s x i x' h1) (@lem4488627 A K _52011 _52012 i x' k s t x h2)). Qed.
Lemma lem4489255 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_52037 : K) (_52038 : A) : (term475 A K k t _52037 _52038) = (term475 A K k t _52037 _52038).
Proof. exact (eq_refl (term475 A K k t _52037 _52038)). Qed.
Lemma lem4489256 {A K : Type'} (_52037 : K) (_52038 : A) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : (term476 A K k t _52037 _52038 x) = (term477 A K k t _52037 _52038 i x').
Proof. exact (MK_COMB (@lem4489255 A K k t _52037 _52038) (@lem4488707 A K k t x i x' h1)). Qed.
Lemma lem4489257 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term477 A K k t _52037 _52038 i x') = (term478 A K k t i x' _52037 _52038).
Proof. exact (eq_refl (term477 A K k t _52037 _52038 i x')). Qed.
Lemma lem4489258 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_52037 : K) (_52038 : A) (x : prod K A) : (term479 A K k t _52037 _52038 x) = (term479 A K k t _52037 _52038 x).
Proof. exact (eq_refl (term479 A K k t _52037 _52038 x)). Qed.
Lemma lem4489259 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : ((term476 A K k t _52037 _52038 x) = (term477 A K k t _52037 _52038 i x')) = ((term476 A K k t _52037 _52038 x) = (term478 A K k t i x' _52037 _52038)).
Proof. exact (MK_COMB (@lem4489258 A K k t _52037 _52038 x) (@lem4489257 A K k t i x' _52037 _52038)). Qed.
Lemma lem4489260 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52037 : K) (_52038 : A) : (term476 A K k t _52037 _52038 x) = (term474 A K k t x _52037 _52038).
Proof. exact (eq_refl (term476 A K k t _52037 _52038 x)). Qed.
Lemma lem4489261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4489262 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52037 : K) (_52038 : A) : (term479 A K k t _52037 _52038 x) = (term480 A K k t x _52037 _52038).
Proof. exact (MK_COMB (@lem4489261) (@lem4489260 A K k t x _52037 _52038)). Qed.
Lemma lem4489263 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term478 A K k t i x' _52037 _52038) = (term478 A K k t i x' _52037 _52038).
Proof. exact (eq_refl (term478 A K k t i x' _52037 _52038)). Qed.
Lemma lem4489264 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : ((term476 A K k t _52037 _52038 x) = (term478 A K k t i x' _52037 _52038)) = ((term474 A K k t x _52037 _52038) = (term478 A K k t i x' _52037 _52038)).
Proof. exact (MK_COMB (@lem4489262 A K k t x _52037 _52038) (@lem4489263 A K k t i x' _52037 _52038)). Qed.
Lemma lem4489265 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : ((term476 A K k t _52037 _52038 x) = (term477 A K k t _52037 _52038 i x')) = ((term474 A K k t x _52037 _52038) = (term478 A K k t i x' _52037 _52038)).
Proof. exact (TRANS (@lem4489259 A K x k t i x' _52037 _52038) (@lem4489264 A K x k t i x' _52037 _52038)). Qed.
Lemma lem4489266 {A K : Type'} (_52037 : K) (_52038 : A) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : (term474 A K k t x _52037 _52038) = (term478 A K k t i x' _52037 _52038).
Proof. exact (EQ_MP (@lem4489265 A K x k t i x' _52037 _52038) (@lem4489256 A K _52037 _52038 k t x i x' h1)). Qed.
Lemma lem4489267 {A K : Type'} (_52037 : K) (_52038 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k t x i x') (h2 : term364 A K i x' k s t x) : term478 A K k t i x' _52037 _52038.
Proof. exact (EQ_MP (@lem4489266 A K _52037 _52038 k t x i x' h1) (@lem4488735 A K _52037 _52038 i x' k s t x h2)). Qed.
Lemma lem4489422 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52063 : K) (_52064 : A) : (term475 A K k s _52063 _52064) = (term475 A K k s _52063 _52064).
Proof. exact (eq_refl (term475 A K k s _52063 _52064)). Qed.
Lemma lem4489423 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : (term476 A K k s _52063 _52064 x) = (term477 A K k s _52063 _52064 i x').
Proof. exact (MK_COMB (@lem4489422 A K k s _52063 _52064) (@lem4488803 A K k s t x i x' h1)). Qed.
Lemma lem4489424 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term477 A K k s _52063 _52064 i x') = (term478 A K k s i x' _52063 _52064).
Proof. exact (eq_refl (term477 A K k s _52063 _52064 i x')). Qed.
Lemma lem4489425 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_52063 : K) (_52064 : A) (x : prod K A) : (term479 A K k s _52063 _52064 x) = (term479 A K k s _52063 _52064 x).
Proof. exact (eq_refl (term479 A K k s _52063 _52064 x)). Qed.
Lemma lem4489426 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : ((term476 A K k s _52063 _52064 x) = (term477 A K k s _52063 _52064 i x')) = ((term476 A K k s _52063 _52064 x) = (term478 A K k s i x' _52063 _52064)).
Proof. exact (MK_COMB (@lem4489425 A K k s _52063 _52064 x) (@lem4489424 A K k s i x' _52063 _52064)). Qed.
Lemma lem4489427 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52063 : K) (_52064 : A) : (term476 A K k s _52063 _52064 x) = (term474 A K k s x _52063 _52064).
Proof. exact (eq_refl (term476 A K k s _52063 _52064 x)). Qed.
Lemma lem4489428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4489429 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_52063 : K) (_52064 : A) : (term479 A K k s _52063 _52064 x) = (term480 A K k s x _52063 _52064).
Proof. exact (MK_COMB (@lem4489428) (@lem4489427 A K k s x _52063 _52064)). Qed.
Lemma lem4489430 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term478 A K k s i x' _52063 _52064) = (term478 A K k s i x' _52063 _52064).
Proof. exact (eq_refl (term478 A K k s i x' _52063 _52064)). Qed.
Lemma lem4489431 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : ((term476 A K k s _52063 _52064 x) = (term478 A K k s i x' _52063 _52064)) = ((term474 A K k s x _52063 _52064) = (term478 A K k s i x' _52063 _52064)).
Proof. exact (MK_COMB (@lem4489429 A K k s x _52063 _52064) (@lem4489430 A K k s i x' _52063 _52064)). Qed.
Lemma lem4489432 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : ((term476 A K k s _52063 _52064 x) = (term477 A K k s _52063 _52064 i x')) = ((term474 A K k s x _52063 _52064) = (term478 A K k s i x' _52063 _52064)).
Proof. exact (TRANS (@lem4489426 A K x k s i x' _52063 _52064) (@lem4489431 A K x k s i x' _52063 _52064)). Qed.
Lemma lem4489433 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : (term474 A K k s x _52063 _52064) = (term478 A K k s i x' _52063 _52064).
Proof. exact (EQ_MP (@lem4489432 A K x k s i x' _52063 _52064) (@lem4489423 A K _52063 _52064 k s t x i x' h1)). Qed.
Lemma lem4489434 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term478 A K k s i x' _52063 _52064.
Proof. exact (EQ_MP (@lem4489433 A K _52063 _52064 k s t x i x' h1) (@lem4488817 A K _52063 _52064 k s t x i x' h1)). Qed.
Lemma lem4489461 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) (h1 : term208 A K x' s i) : term208 A K x' s i.
Proof. exact (h1). Qed.
Lemma lem4489629 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_52093 : K) (_52094 : A) : (term475 A K k t _52093 _52094) = (term475 A K k t _52093 _52094).
Proof. exact (eq_refl (term475 A K k t _52093 _52094)). Qed.
Lemma lem4489630 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : (term476 A K k t _52093 _52094 x) = (term477 A K k t _52093 _52094 i x').
Proof. exact (MK_COMB (@lem4489629 A K k t _52093 _52094) (@lem4488899 A K k s t x i x' h1)). Qed.
Lemma lem4489631 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term477 A K k t _52093 _52094 i x') = (term478 A K k t i x' _52093 _52094).
Proof. exact (eq_refl (term477 A K k t _52093 _52094 i x')). Qed.
Lemma lem4489632 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_52093 : K) (_52094 : A) (x : prod K A) : (term479 A K k t _52093 _52094 x) = (term479 A K k t _52093 _52094 x).
Proof. exact (eq_refl (term479 A K k t _52093 _52094 x)). Qed.
Lemma lem4489633 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : ((term476 A K k t _52093 _52094 x) = (term477 A K k t _52093 _52094 i x')) = ((term476 A K k t _52093 _52094 x) = (term478 A K k t i x' _52093 _52094)).
Proof. exact (MK_COMB (@lem4489632 A K k t _52093 _52094 x) (@lem4489631 A K k t i x' _52093 _52094)). Qed.
Lemma lem4489634 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52093 : K) (_52094 : A) : (term476 A K k t _52093 _52094 x) = (term474 A K k t x _52093 _52094).
Proof. exact (eq_refl (term476 A K k t _52093 _52094 x)). Qed.
Lemma lem4489635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4489636 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_52093 : K) (_52094 : A) : (term479 A K k t _52093 _52094 x) = (term480 A K k t x _52093 _52094).
Proof. exact (MK_COMB (@lem4489635) (@lem4489634 A K k t x _52093 _52094)). Qed.
Lemma lem4489637 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term478 A K k t i x' _52093 _52094) = (term478 A K k t i x' _52093 _52094).
Proof. exact (eq_refl (term478 A K k t i x' _52093 _52094)). Qed.
Lemma lem4489638 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : ((term476 A K k t _52093 _52094 x) = (term478 A K k t i x' _52093 _52094)) = ((term474 A K k t x _52093 _52094) = (term478 A K k t i x' _52093 _52094)).
Proof. exact (MK_COMB (@lem4489636 A K k t x _52093 _52094) (@lem4489637 A K k t i x' _52093 _52094)). Qed.
Lemma lem4489639 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : ((term476 A K k t _52093 _52094 x) = (term477 A K k t _52093 _52094 i x')) = ((term474 A K k t x _52093 _52094) = (term478 A K k t i x' _52093 _52094)).
Proof. exact (TRANS (@lem4489633 A K x k t i x' _52093 _52094) (@lem4489638 A K x k t i x' _52093 _52094)). Qed.
Lemma lem4489640 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : (term474 A K k t x _52093 _52094) = (term478 A K k t i x' _52093 _52094).
Proof. exact (EQ_MP (@lem4489639 A K x k t i x' _52093 _52094) (@lem4489630 A K _52093 _52094 k s t x i x' h1)). Qed.
Lemma lem4489641 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term478 A K k t i x' _52093 _52094.
Proof. exact (EQ_MP (@lem4489640 A K _52093 _52094 k s t x i x' h1) (@lem4488925 A K _52093 _52094 k s t x i x' h1)). Qed.
Lemma lem4489655 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) (h1 : term208 A K x' t i) : term208 A K x' t i.
Proof. exact (h1). Qed.
Lemma lem4489856 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : @IN K i k.
Proof. exact (proj1 (@lem4487279 A K k s x i x' h1)). Qed.
Lemma lem4489857 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term481 K i k.
Proof. exact (fun h0 : term462 K i k => @lem4489856 A K k s x i x' h1). Qed.
Lemma lem4489859 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4489860 {K : Type'} (i : K) (k : K -> Prop) : (term481 K i k) = (@IN K i k).
Proof. exact (@lem4489859 (@IN K i k)). Qed.
Lemma lem4489861 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : @IN K i k.
Proof. exact (EQ_MP (@lem4489860 K i k) (@lem4489857 A K k s x i x' h1)). Qed.
Lemma lem4489863 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term208 A K x' s i.
Proof. exact (proj2 (@lem4487279 A K k s x i x' h1)). Qed.
Lemma lem4489864 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term483 A K x' s i.
Proof. exact (fun h0 : term461 A K x' s i => @lem4489863 A K k s x i x' h1). Qed.
Lemma lem4489866 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4489867 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) : (term483 A K x' s i) = (term208 A K x' s i).
Proof. exact (@lem4489866 (term208 A K x' s i)). Qed.
Lemma lem4489868 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term208 A K x' s i.
Proof. exact (EQ_MP (@lem4489867 A K x' s i) (@lem4489864 A K k s x i x' h1)). Qed.
Lemma lem4489870 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem21386 (prod K A) x). Qed.
Lemma lem4489871 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem4489870 A K x). Qed.
Lemma lem4489872 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (@lem4489871 A K (@pair K A i x')). Qed.
Lemma lem4489873 {A K : Type'} (i : K) (x' : A) : term484 A K i x'.
Proof. exact (fun h0 : term485 A K i x' => @lem4489872 A K i x'). Qed.
Lemma lem4489875 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4489876 {A K : Type'} (i : K) (x' : A) : (term484 A K i x') = ((@pair K A i x') = (@pair K A i x')).
Proof. exact (@lem4489875 ((@pair K A i x') = (@pair K A i x'))). Qed.
Lemma lem4489877 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (EQ_MP (@lem4489876 A K i x') (@lem4489873 A K i x')). Qed.
Lemma lem4489879 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4489880 {A K : Type'} (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term488 A K s i x' _52011 _52012) = (term489 A K s i x' _52011 _52012).
Proof. exact (@lem4489879 (term208 A K _52012 s _52011) ((@pair K A i x') = (@pair K A _52011 _52012))). Qed.
Lemma lem4489881 {K : Type'} (_52011 : K) (k : K -> Prop) : (term238 K _52011 k) = (term238 K _52011 k).
Proof. exact (eq_refl (term238 K _52011 k)). Qed.
Lemma lem4489882 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term478 A K k s i x' _52011 _52012) = (term490 A K k s i x' _52011 _52012).
Proof. exact (MK_COMB (@lem4489881 K _52011 k) (@lem4489880 A K s i x' _52011 _52012)). Qed.
Lemma lem4489884 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4489885 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term490 A K k s i x' _52011 _52012) = (term491 A K k s i x' _52011 _52012).
Proof. exact (@lem4489884 (@IN K _52011 k) (term492 A K s i x' _52011 _52012)). Qed.
Lemma lem4489886 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term478 A K k s i x' _52011 _52012) = (term491 A K k s i x' _52011 _52012).
Proof. exact (TRANS (@lem4489882 A K k s i x' _52011 _52012) (@lem4489885 A K k s i x' _52011 _52012)). Qed.
Lemma lem4489888 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4489889 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term491 A K k s i x' _52011 _52012) = (term493 A K k s i x' _52011 _52012).
Proof. exact (@lem4489888 (term494 A K k s i x' _52011 _52012)). Qed.
Lemma lem4489890 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52011 : K) (_52012 : A) : (term478 A K k s i x' _52011 _52012) = (term493 A K k s i x' _52011 _52012).
Proof. exact (TRANS (@lem4489886 A K k s i x' _52011 _52012) (@lem4489889 A K k s i x' _52011 _52012)). Qed.
Lemma lem4489892 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term495 A K s i x'.
Proof. exact (conj (@lem4489868 A K k s x i x' h1) (@lem4489877 A K i x')). Qed.
Lemma lem4489893 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k s x i x') : term496 A K k s i x'.
Proof. exact (conj (@lem4489861 A K k s x i x' h1) (@lem4489892 A K k s x i x' h1)). Qed.
Lemma lem4489895 {A K : Type'} (_52011 : K) (_52012 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k s x i x') (h2 : term364 A K i x' k s t x) : term493 A K k s i x' _52011 _52012.
Proof. exact (EQ_MP (@lem4489890 A K k s i x' _52011 _52012) (@lem4489060 A K _52011 _52012 i x' k s t x h1 h2)). Qed.
Lemma lem4489896 {A K : Type'} (_52011 : K) (_52012 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k s x i x') (h2 : term364 A K i x' k s t x) : term493 A K k s i x' _52011 _52012.
Proof. exact (@lem4489895 A K _52011 _52012 i x' k s t x h1 h2). Qed.
Lemma lem4489897 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k s x i x') (h2 : term364 A K i x' k s t x) : term497 A K k s i x'.
Proof. exact (@lem4489896 A K i x' i x' k s t x h1 h2). Qed.
Lemma lem4489900 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k s x i x') (h2 : term364 A K i x' k s t x) : False.
Proof. exact (@lem4489897 A K i x' k s t x h1 h2 (@lem4489893 A K k s x i x' h1)). Qed.
Lemma lem4489901 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k s x i x') (h2 : term364 A K i x' k s t x) : term498.
Proof. exact (fun h0 : ~ False => @lem4489900 A K i x' k s t x h1 h2). Qed.
Lemma lem4489903 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4489904 : term498 = False.
Proof. exact (@lem4489903 False). Qed.
Lemma lem4490022 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : @IN K i k.
Proof. exact (proj1 (@lem4487283 A K k t x i x' h1)). Qed.
Lemma lem4490023 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term481 K i k.
Proof. exact (fun h0 : term462 K i k => @lem4490022 A K k t x i x' h1). Qed.
Lemma lem4490025 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490026 {K : Type'} (i : K) (k : K -> Prop) : (term481 K i k) = (@IN K i k).
Proof. exact (@lem4490025 (@IN K i k)). Qed.
Lemma lem4490027 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : @IN K i k.
Proof. exact (EQ_MP (@lem4490026 K i k) (@lem4490023 A K k t x i x' h1)). Qed.
Lemma lem4490029 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term208 A K x' t i.
Proof. exact (proj2 (@lem4487283 A K k t x i x' h1)). Qed.
Lemma lem4490030 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term483 A K x' t i.
Proof. exact (fun h0 : term461 A K x' t i => @lem4490029 A K k t x i x' h1). Qed.
Lemma lem4490032 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490033 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) : (term483 A K x' t i) = (term208 A K x' t i).
Proof. exact (@lem4490032 (term208 A K x' t i)). Qed.
Lemma lem4490034 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term208 A K x' t i.
Proof. exact (EQ_MP (@lem4490033 A K x' t i) (@lem4490030 A K k t x i x' h1)). Qed.
Lemma lem4490036 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem21386 (prod K A) x). Qed.
Lemma lem4490037 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem4490036 A K x). Qed.
Lemma lem4490038 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (@lem4490037 A K (@pair K A i x')). Qed.
Lemma lem4490039 {A K : Type'} (i : K) (x' : A) : term484 A K i x'.
Proof. exact (fun h0 : term485 A K i x' => @lem4490038 A K i x'). Qed.
Lemma lem4490041 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490042 {A K : Type'} (i : K) (x' : A) : (term484 A K i x') = ((@pair K A i x') = (@pair K A i x')).
Proof. exact (@lem4490041 ((@pair K A i x') = (@pair K A i x'))). Qed.
Lemma lem4490043 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (EQ_MP (@lem4490042 A K i x') (@lem4490039 A K i x')). Qed.
Lemma lem4490045 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4490046 {A K : Type'} (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term488 A K t i x' _52037 _52038) = (term489 A K t i x' _52037 _52038).
Proof. exact (@lem4490045 (term208 A K _52038 t _52037) ((@pair K A i x') = (@pair K A _52037 _52038))). Qed.
Lemma lem4490047 {K : Type'} (_52037 : K) (k : K -> Prop) : (term238 K _52037 k) = (term238 K _52037 k).
Proof. exact (eq_refl (term238 K _52037 k)). Qed.
Lemma lem4490048 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term478 A K k t i x' _52037 _52038) = (term490 A K k t i x' _52037 _52038).
Proof. exact (MK_COMB (@lem4490047 K _52037 k) (@lem4490046 A K t i x' _52037 _52038)). Qed.
Lemma lem4490050 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4490051 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term490 A K k t i x' _52037 _52038) = (term491 A K k t i x' _52037 _52038).
Proof. exact (@lem4490050 (@IN K _52037 k) (term492 A K t i x' _52037 _52038)). Qed.
Lemma lem4490052 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term478 A K k t i x' _52037 _52038) = (term491 A K k t i x' _52037 _52038).
Proof. exact (TRANS (@lem4490048 A K k t i x' _52037 _52038) (@lem4490051 A K k t i x' _52037 _52038)). Qed.
Lemma lem4490054 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4490055 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term491 A K k t i x' _52037 _52038) = (term493 A K k t i x' _52037 _52038).
Proof. exact (@lem4490054 (term494 A K k t i x' _52037 _52038)). Qed.
Lemma lem4490056 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52037 : K) (_52038 : A) : (term478 A K k t i x' _52037 _52038) = (term493 A K k t i x' _52037 _52038).
Proof. exact (TRANS (@lem4490052 A K k t i x' _52037 _52038) (@lem4490055 A K k t i x' _52037 _52038)). Qed.
Lemma lem4490058 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term495 A K t i x'.
Proof. exact (conj (@lem4490034 A K k t x i x' h1) (@lem4490043 A K i x')). Qed.
Lemma lem4490059 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term72 A K k t x i x') : term496 A K k t i x'.
Proof. exact (conj (@lem4490027 A K k t x i x' h1) (@lem4490058 A K k t x i x' h1)). Qed.
Lemma lem4490061 {A K : Type'} (_52037 : K) (_52038 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k t x i x') (h2 : term364 A K i x' k s t x) : term493 A K k t i x' _52037 _52038.
Proof. exact (EQ_MP (@lem4490056 A K k t i x' _52037 _52038) (@lem4489267 A K _52037 _52038 i x' k s t x h1 h2)). Qed.
Lemma lem4490062 {A K : Type'} (_52037 : K) (_52038 : A) (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k t x i x') (h2 : term364 A K i x' k s t x) : term493 A K k t i x' _52037 _52038.
Proof. exact (@lem4490061 A K _52037 _52038 i x' k s t x h1 h2). Qed.
Lemma lem4490063 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k t x i x') (h2 : term364 A K i x' k s t x) : term497 A K k t i x'.
Proof. exact (@lem4490062 A K i x' i x' k s t x h1 h2). Qed.
Lemma lem4490066 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k t x i x') (h2 : term364 A K i x' k s t x) : False.
Proof. exact (@lem4490063 A K i x' k s t x h1 h2 (@lem4490059 A K k t x i x' h1)). Qed.
Lemma lem4490067 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k t x i x') (h2 : term364 A K i x' k s t x) : term498.
Proof. exact (fun h0 : ~ False => @lem4490066 A K i x' k s t x h1 h2). Qed.
Lemma lem4490069 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490070 : term498 = False.
Proof. exact (@lem4490069 False). Qed.
Lemma lem4490188 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : @IN K i k.
Proof. exact (proj1 (@lem4487289 A K k s t x i x' h1)). Qed.
Lemma lem4490189 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term481 K i k.
Proof. exact (fun h0 : term462 K i k => @lem4490188 A K k s t x i x' h1). Qed.
Lemma lem4490191 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490192 {K : Type'} (i : K) (k : K -> Prop) : (term481 K i k) = (@IN K i k).
Proof. exact (@lem4490191 (@IN K i k)). Qed.
Lemma lem4490193 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : @IN K i k.
Proof. exact (EQ_MP (@lem4490192 K i k) (@lem4490189 A K k s t x i x' h1)). Qed.
Lemma lem4490195 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) (h1 : term208 A K x' s i) : term208 A K x' s i.
Proof. exact (h1). Qed.
Lemma lem4490196 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) (h1 : term208 A K x' s i) : term483 A K x' s i.
Proof. exact (fun h0 : term461 A K x' s i => @lem4490195 A K x' s i h1). Qed.
Lemma lem4490198 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490199 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) : (term483 A K x' s i) = (term208 A K x' s i).
Proof. exact (@lem4490198 (term208 A K x' s i)). Qed.
Lemma lem4490200 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) (h1 : term208 A K x' s i) : term208 A K x' s i.
Proof. exact (EQ_MP (@lem4490199 A K x' s i) (@lem4490196 A K x' s i h1)). Qed.
Lemma lem4490202 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem21386 (prod K A) x). Qed.
Lemma lem4490203 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem4490202 A K x). Qed.
Lemma lem4490204 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (@lem4490203 A K (@pair K A i x')). Qed.
Lemma lem4490205 {A K : Type'} (i : K) (x' : A) : term484 A K i x'.
Proof. exact (fun h0 : term485 A K i x' => @lem4490204 A K i x'). Qed.
Lemma lem4490207 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490208 {A K : Type'} (i : K) (x' : A) : (term484 A K i x') = ((@pair K A i x') = (@pair K A i x')).
Proof. exact (@lem4490207 ((@pair K A i x') = (@pair K A i x'))). Qed.
Lemma lem4490209 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (EQ_MP (@lem4490208 A K i x') (@lem4490205 A K i x')). Qed.
Lemma lem4490211 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4490212 {A K : Type'} (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term488 A K s i x' _52063 _52064) = (term489 A K s i x' _52063 _52064).
Proof. exact (@lem4490211 (term208 A K _52064 s _52063) ((@pair K A i x') = (@pair K A _52063 _52064))). Qed.
Lemma lem4490213 {K : Type'} (_52063 : K) (k : K -> Prop) : (term238 K _52063 k) = (term238 K _52063 k).
Proof. exact (eq_refl (term238 K _52063 k)). Qed.
Lemma lem4490214 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term478 A K k s i x' _52063 _52064) = (term490 A K k s i x' _52063 _52064).
Proof. exact (MK_COMB (@lem4490213 K _52063 k) (@lem4490212 A K s i x' _52063 _52064)). Qed.
Lemma lem4490216 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4490217 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term490 A K k s i x' _52063 _52064) = (term491 A K k s i x' _52063 _52064).
Proof. exact (@lem4490216 (@IN K _52063 k) (term492 A K s i x' _52063 _52064)). Qed.
Lemma lem4490218 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term478 A K k s i x' _52063 _52064) = (term491 A K k s i x' _52063 _52064).
Proof. exact (TRANS (@lem4490214 A K k s i x' _52063 _52064) (@lem4490217 A K k s i x' _52063 _52064)). Qed.
Lemma lem4490220 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4490221 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term491 A K k s i x' _52063 _52064) = (term493 A K k s i x' _52063 _52064).
Proof. exact (@lem4490220 (term494 A K k s i x' _52063 _52064)). Qed.
Lemma lem4490222 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_52063 : K) (_52064 : A) : (term478 A K k s i x' _52063 _52064) = (term493 A K k s i x' _52063 _52064).
Proof. exact (TRANS (@lem4490218 A K k s i x' _52063 _52064) (@lem4490221 A K k s i x' _52063 _52064)). Qed.
Lemma lem4490224 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) (h1 : term208 A K x' s i) : term495 A K s i x'.
Proof. exact (conj (@lem4490200 A K x' s i h1) (@lem4490209 A K i x')). Qed.
Lemma lem4490225 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : term496 A K k s i x'.
Proof. exact (conj (@lem4490193 A K k s t x i x' h1) (@lem4490224 A K x' s i h2)). Qed.
Lemma lem4490227 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term493 A K k s i x' _52063 _52064.
Proof. exact (EQ_MP (@lem4490222 A K k s i x' _52063 _52064) (@lem4489434 A K _52063 _52064 k s t x i x' h1)). Qed.
Lemma lem4490228 {A K : Type'} (_52063 : K) (_52064 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term493 A K k s i x' _52063 _52064.
Proof. exact (@lem4490227 A K _52063 _52064 k s t x i x' h1). Qed.
Lemma lem4490229 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term497 A K k s i x'.
Proof. exact (@lem4490228 A K i x' k s t x i x' h1). Qed.
Lemma lem4490232 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : False.
Proof. exact (@lem4490229 A K k s t x i x' h1 (@lem4490225 A K k t x x' s i h1 h2)). Qed.
Lemma lem4490233 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : term498.
Proof. exact (fun h0 : ~ False => @lem4490232 A K k t x x' s i h1 h2). Qed.
Lemma lem4490235 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490236 : term498 = False.
Proof. exact (@lem4490235 False). Qed.
Lemma lem4490237 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : False.
Proof. exact (EQ_MP (@lem4490236) (@lem4490233 A K k t x x' s i h1 h2)). Qed.
Lemma lem4490354 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : @IN K i k.
Proof. exact (proj1 (@lem4487289 A K k s t x i x' h1)). Qed.
Lemma lem4490355 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term481 K i k.
Proof. exact (fun h0 : term462 K i k => @lem4490354 A K k s t x i x' h1). Qed.
Lemma lem4490357 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490358 {K : Type'} (i : K) (k : K -> Prop) : (term481 K i k) = (@IN K i k).
Proof. exact (@lem4490357 (@IN K i k)). Qed.
Lemma lem4490359 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : @IN K i k.
Proof. exact (EQ_MP (@lem4490358 K i k) (@lem4490355 A K k s t x i x' h1)). Qed.
Lemma lem4490361 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) (h1 : term208 A K x' t i) : term208 A K x' t i.
Proof. exact (h1). Qed.
Lemma lem4490362 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) (h1 : term208 A K x' t i) : term483 A K x' t i.
Proof. exact (fun h0 : term461 A K x' t i => @lem4490361 A K x' t i h1). Qed.
Lemma lem4490364 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490365 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) : (term483 A K x' t i) = (term208 A K x' t i).
Proof. exact (@lem4490364 (term208 A K x' t i)). Qed.
Lemma lem4490366 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) (h1 : term208 A K x' t i) : term208 A K x' t i.
Proof. exact (EQ_MP (@lem4490365 A K x' t i) (@lem4490362 A K x' t i h1)). Qed.
Lemma lem4490368 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem21386 (prod K A) x). Qed.
Lemma lem4490369 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem4490368 A K x). Qed.
Lemma lem4490370 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (@lem4490369 A K (@pair K A i x')). Qed.
Lemma lem4490371 {A K : Type'} (i : K) (x' : A) : term484 A K i x'.
Proof. exact (fun h0 : term485 A K i x' => @lem4490370 A K i x'). Qed.
Lemma lem4490373 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490374 {A K : Type'} (i : K) (x' : A) : (term484 A K i x') = ((@pair K A i x') = (@pair K A i x')).
Proof. exact (@lem4490373 ((@pair K A i x') = (@pair K A i x'))). Qed.
Lemma lem4490375 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (EQ_MP (@lem4490374 A K i x') (@lem4490371 A K i x')). Qed.
Lemma lem4490377 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4490378 {A K : Type'} (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term488 A K t i x' _52093 _52094) = (term489 A K t i x' _52093 _52094).
Proof. exact (@lem4490377 (term208 A K _52094 t _52093) ((@pair K A i x') = (@pair K A _52093 _52094))). Qed.
Lemma lem4490379 {K : Type'} (_52093 : K) (k : K -> Prop) : (term238 K _52093 k) = (term238 K _52093 k).
Proof. exact (eq_refl (term238 K _52093 k)). Qed.
Lemma lem4490380 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term478 A K k t i x' _52093 _52094) = (term490 A K k t i x' _52093 _52094).
Proof. exact (MK_COMB (@lem4490379 K _52093 k) (@lem4490378 A K t i x' _52093 _52094)). Qed.
Lemma lem4490382 (a : Prop) (b : Prop) : (term486 a b) = (term487 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4490383 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term490 A K k t i x' _52093 _52094) = (term491 A K k t i x' _52093 _52094).
Proof. exact (@lem4490382 (@IN K _52093 k) (term492 A K t i x' _52093 _52094)). Qed.
Lemma lem4490384 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term478 A K k t i x' _52093 _52094) = (term491 A K k t i x' _52093 _52094).
Proof. exact (TRANS (@lem4490380 A K k t i x' _52093 _52094) (@lem4490383 A K k t i x' _52093 _52094)). Qed.
Lemma lem4490386 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4490387 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term491 A K k t i x' _52093 _52094) = (term493 A K k t i x' _52093 _52094).
Proof. exact (@lem4490386 (term494 A K k t i x' _52093 _52094)). Qed.
Lemma lem4490388 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_52093 : K) (_52094 : A) : (term478 A K k t i x' _52093 _52094) = (term493 A K k t i x' _52093 _52094).
Proof. exact (TRANS (@lem4490384 A K k t i x' _52093 _52094) (@lem4490387 A K k t i x' _52093 _52094)). Qed.
Lemma lem4490390 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) (h1 : term208 A K x' t i) : term495 A K t i x'.
Proof. exact (conj (@lem4490366 A K x' t i h1) (@lem4490375 A K i x')). Qed.
Lemma lem4490391 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : term496 A K k t i x'.
Proof. exact (conj (@lem4490359 A K k s t x i x' h1) (@lem4490390 A K x' t i h2)). Qed.
Lemma lem4490393 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term493 A K k t i x' _52093 _52094.
Proof. exact (EQ_MP (@lem4490388 A K k t i x' _52093 _52094) (@lem4489641 A K _52093 _52094 k s t x i x' h1)). Qed.
Lemma lem4490394 {A K : Type'} (_52093 : K) (_52094 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term493 A K k t i x' _52093 _52094.
Proof. exact (@lem4490393 A K _52093 _52094 k s t x i x' h1). Qed.
Lemma lem4490395 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : term497 A K k t i x'.
Proof. exact (@lem4490394 A K i x' k s t x i x' h1). Qed.
Lemma lem4490398 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : False.
Proof. exact (@lem4490395 A K k s t x i x' h1 (@lem4490391 A K k s x x' t i h1 h2)). Qed.
Lemma lem4490399 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : term498.
Proof. exact (fun h0 : ~ False => @lem4490398 A K k s x x' t i h1 h2). Qed.
Lemma lem4490401 (p : Prop) : (term482 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4490402 : term498 = False.
Proof. exact (@lem4490401 False). Qed.
Lemma lem4490403 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : False.
Proof. exact (EQ_MP (@lem4490402) (@lem4490399 A K k s x x' t i h1 h2)). Qed.
Lemma lem4490404 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : (term208 A K x' t i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' t i => @lem4490403 A K k s x x' t i h1 h2) (fun h3 : False => @lem4489655 A K x' t i h2)). Qed.
Lemma lem4490406 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : False.
Proof. exact (EQ_MP (@lem4490404 A K k s x x' t i h1 h2) (@lem4489655 A K x' t i h2)). Qed.
Lemma lem4490407 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : (term208 A K x' s i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' s i => @lem4490237 A K k t x x' s i h1 h2) (fun h3 : False => @lem4489461 A K x' s i h2)). Qed.
Lemma lem4490409 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : False.
Proof. exact (EQ_MP (@lem4490407 A K k t x x' s i h1 h2) (@lem4489461 A K x' s i h2)). Qed.
Lemma lem4490410 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k t x i x') (h2 : term364 A K i x' k s t x) : False.
Proof. exact (EQ_MP (@lem4490070) (@lem4490067 A K i x' k s t x h1 h2)). Qed.
Lemma lem4490411 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term72 A K k s x i x') (h2 : term364 A K i x' k s t x) : False.
Proof. exact (EQ_MP (@lem4489904) (@lem4489901 A K i x' k s t x h1 h2)). Qed.
Lemma lem4490412 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : (term208 A K x' t i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' t i => @lem4490406 A K k s x x' t i h1 h2) (fun h3 : False => @lem4488927 A K x' t i h2)). Qed.
Lemma lem4490413 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : False.
Proof. exact (EQ_MP (@lem4490412 A K k s x x' t i h1 h2) (@lem4488927 A K x' t i h2)). Qed.
Lemma lem4490414 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : (term208 A K x' s i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' s i => @lem4490409 A K k t x x' s i h1 h2) (fun h3 : False => @lem4488831 A K x' s i h2)). Qed.
Lemma lem4490415 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : False.
Proof. exact (EQ_MP (@lem4490414 A K k t x x' s i h1 h2) (@lem4488831 A K x' s i h2)). Qed.
Lemma lem4490416 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : (term208 A K x' t i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' t i => @lem4490413 A K k s x x' t i h1 h2) (fun h3 : False => @lem4488227 A K x' t i h2)). Qed.
Lemma lem4490417 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : False.
Proof. exact (EQ_MP (@lem4490416 A K k s x x' t i h1 h2) (@lem4488227 A K x' t i h2)). Qed.
Lemma lem4490418 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : (term208 A K x' s i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' s i => @lem4490415 A K k t x x' s i h1 h2) (fun h3 : False => @lem4487991 A K x' s i h2)). Qed.
Lemma lem4490419 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : False.
Proof. exact (EQ_MP (@lem4490418 A K k t x x' s i h1 h2) (@lem4487991 A K x' s i h2)). Qed.
Lemma lem4490420 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : (term208 A K x' t i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' t i => @lem4490417 A K k s x x' t i h1 h2) (fun h3 : False => @lem4488227 A K x' t i h2)). Qed.
Lemma lem4490421 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (x' : A) (t : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' t i) : False.
Proof. exact (EQ_MP (@lem4490420 A K k s x x' t i h1 h2) (@lem4488227 A K x' t i h2)). Qed.
Lemma lem4490422 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : (term208 A K x' s i) = False.
Proof. exact (prop_ext (fun h3 : term208 A K x' s i => @lem4490419 A K k t x x' s i h1 h2) (fun h3 : False => @lem4487991 A K x' s i h2)). Qed.
Lemma lem4490423 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (x' : A) (s : type1470 A K) (i : K) (h1 : term393 A K k s t x i x') (h2 : term208 A K x' s i) : False.
Proof. exact (EQ_MP (@lem4490422 A K k t x x' s i h1 h2) (@lem4487991 A K x' s i h2)). Qed.
Lemma lem4490424 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term393 A K k s t x i x') : False.
Proof. exact (or_elim (@lem4487290 A K k s t x i x' h1) (fun h0 : term208 A K x' s i => @lem4490423 A K k t x x' s i h1 h0) (fun h0 : term208 A K x' t i => @lem4490421 A K k s x x' t i h1 h0)). Qed.
Lemma lem4490425 {A K : Type'} (i : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term364 A K i x' k s t x) : False.
Proof. exact (or_elim (@lem4487275 A K i x' k s t x h1) (fun h0 : term72 A K k s x i x' => @lem4490411 A K i x' k s t x h0 h1) (fun h0 : term72 A K k t x i x' => @lem4490410 A K i x' k s t x h0 h1)). Qed.
Lemma lem4490426 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term452 A K k s t x i x') : False.
Proof. exact (or_elim (@lem4487265 A K k s t x i x' h1) (fun h0 : term364 A K i x' k s t x => @lem4490425 A K i x' k s t x h0) (fun h0 : term393 A K k s t x i x' => @lem4490424 A K k s t x i x' h0)). Qed.
Lemma lem4490427 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term452 A K k s t x i x') : (term452 A K k s t x i x') = False.
Proof. exact (prop_ext (fun h2 : term452 A K k s t x i x' => @lem4490426 A K k s t x i x' h1) (fun h2 : False => @lem4487265 A K k s t x i x' h1)). Qed.
Lemma lem4490428 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term452 A K k s t x i x') : False.
Proof. exact (EQ_MP (@lem4490427 A K k s t x i x' h1) (@lem4487265 A K k s t x i x' h1)). Qed.
Lemma lem4490429 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (h1 : term455 A K k s t x i) : False.
Proof. exact (ex_elim (@lem4486752 A K k s t x i h1) (fun x' : A => fun h0 : term454 A K k s t x i x' => @lem4490428 A K k s t x i x' h0)). Qed.
Lemma lem4490430 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term457 A K k s t x) : False.
Proof. exact (ex_elim (@lem4486751 A K k s t x h1) (fun i : K => fun h0 : term456 A K k s t x i => @lem4490429 A K k s t x i h0)). Qed.
Lemma lem4490431 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : False.
Proof. exact (ex_elim (@lem4484935 A K k s t h1) (fun x : prod K A => fun h0 : term458 A K k s t x => @lem4490430 A K k s t x h0)). Qed.
Lemma lem4490432 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term160 A B K.
Proof. exact (fun h0 : term154 A B K => @lem4490431 A K k s t h1). Qed.
Lemma lem4490433 {A B K : Type'} : (term160 A B K) = (term161 A B K).
Proof. exact (@lem69 (term154 A B K)). Qed.
Lemma lem4490434 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term161 A B K.
Proof. exact (EQ_MP (@lem4490433 A B K) (@lem4490432 A B K k s t h1)). Qed.
Lemma lem4490435 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term164 A B K.
Proof. exact (fun h0 : term153 A K => @lem4490434 A B K k s t h1). Qed.
Lemma lem4490436 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term167 A B K.
Proof. exact (fun h0 : term155 A K => @lem4490435 A B K k s t h1). Qed.
Lemma lem4490437 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term169 A B K k s t.
Proof. exact (fun h0 : term152 A K k s t => @lem4490436 A B K k s t h0). Qed.
Lemma lem4490442 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : term173 A B K s t.
Proof. exact (fun k : K -> Prop => @lem4490437 A B K k s t). Qed.
Lemma lem4490447 {A B K : Type'} (t : type1470 A K) : term177 A B K t.
Proof. exact (fun s : type1470 A K => @lem4490442 A B K s t). Qed.
Lemma lem4490452 {A B K : Type'} : term181 A B K.
Proof. exact (fun t : type1470 A K => @lem4490447 A B K t). Qed.
Lemma lem4490453 {A B K : Type'} : term180 A B K.
Proof. exact (EQ_MP (@lem4484052 A B K) (@lem4490452 A B K)). Qed.
Lemma lem4490454 {A B K : Type'} (t : type1470 A K) : term499 A B K t.
Proof. exact (@lem4490453 A B K t). Qed.
Lemma lem4490455 {A B K : Type'} (t : type1470 A K) : (term499 A B K t) = (term176 A B K t).
Proof. exact (eq_refl (term499 A B K t)). Qed.
Lemma lem4490456 {A B K : Type'} (t : type1470 A K) : term176 A B K t.
Proof. exact (EQ_MP (@lem4490455 A B K t) (@lem4490454 A B K t)). Qed.
Lemma lem4490457 {A B K : Type'} (t : type1470 A K) (s : type1470 A K) : term500 A B K t s.
Proof. exact (@lem4490456 A B K t s). Qed.
Lemma lem4490458 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term500 A B K t s) = (term172 A B K s t).
Proof. exact (eq_refl (term500 A B K t s)). Qed.
Lemma lem4490459 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : term172 A B K s t.
Proof. exact (EQ_MP (@lem4490458 A B K s t) (@lem4490457 A B K t s)). Qed.
Lemma lem4490460 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : term501 A B K s t k.
Proof. exact (@lem4490459 A B K s t k). Qed.
Lemma lem4490461 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term501 A B K s t k) = (term156 A B K k s t).
Proof. exact (eq_refl (term501 A B K s t k)). Qed.
Lemma lem4490462 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term156 A B K k s t.
Proof. exact (EQ_MP (@lem4490461 A B K k s t) (@lem4490460 A B K s t k)). Qed.
Lemma lem4490464 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term156 A B K k s t.
Proof. exact (@lem4483457 A B K k s t (@lem4490462 A B K k s t)). Qed.
Lemma lem4490465 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term166 A B K.
Proof. exact (@lem4490464 A B K k s t (@lem4483437 A K k s t h1)). Qed.
Lemma lem4490466 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term163 A B K.
Proof. exact (@lem4490465 A B K k s t h1 (@lem4483441 A K)). Qed.
Lemma lem4490467 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term160 A B K.
Proof. exact (@lem4490466 A B K k s t h1 (@lem4483438 A K)). Qed.
Lemma lem4490468 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : False.
Proof. exact (@lem4490467 A Prop K k s t h1 (@lem4483440 A Prop K)). Qed.
Lemma lem4490469 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : (term152 A K k s t) = False.
Proof. exact (prop_ext (fun h2 : term152 A K k s t => @lem4490468 A K k s t h1) (fun h2 : False => @lem4483437 A K k s t h1)). Qed.
Lemma lem4490470 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : False.
Proof. exact (EQ_MP (@lem4490469 A K k s t h1) (@lem4483437 A K k s t h1)). Qed.
Lemma lem4490471 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term151 A K k s t.
Proof. exact (fun h0 : term152 A K k s t => @lem4490470 A K k s t h0). Qed.
Lemma lem4490472 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term149 A K k s t.
Proof. exact (EQ_MP (@lem4483436 A K k s t) (@lem4490471 A K k s t)). Qed.
Lemma lem4490473 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term29 A K s k t) = (term30 A K k s t).
Proof. exact (EQ_MP (@lem4483432 A K k s t) (@lem4490472 A K k s t)). Qed.
Lemma lem4490478 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term502 A K k s.
Proof. exact (fun t : type1470 A K => @lem4490473 A K k s t). Qed.
Lemma lem4490483 {A K : Type'} (k : K -> Prop) : term503 A K k.
Proof. exact (fun s : type1470 A K => @lem4490478 A K k s). Qed.
Lemma lem4490488 {A K : Type'} : term504 A K.
Proof. exact (fun k : K -> Prop => @lem4490483 A K k). Qed.
