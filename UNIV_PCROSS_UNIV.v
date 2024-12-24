Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIV_PCROSS_UNIV_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_UNIV_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm7_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8026004 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem8026005 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem8026006 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem8026005 A x) (@lem8026004 A x)). Qed.
Lemma lem8026007 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem8026009 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8026010 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term1 _141927 _141928 _141929 s) = (term2 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term1 _141927 _141928 _141929 s)). Qed.
Lemma lem8026011 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term2 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8026010 _141927 _141928 _141929 s) (@lem8026009 _141927 _141928 _141929 s)). Qed.
Lemma lem8026012 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (@lem8026011 _141927 _141928 _141929 s t). Qed.
Lemma lem8026013 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term3 _141927 _141928 _141929 s t) = (term4 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term3 _141927 _141928 _141929 s t)). Qed.
Lemma lem8026014 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term4 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8026013 _141927 _141928 _141929 s t) (@lem8026012 _141927 _141928 _141929 s t)). Qed.
Lemma lem8026015 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term5 _141927 _141928 _141929 s t x.
Proof. exact (@lem8026014 _141927 _141928 _141929 s t x). Qed.
Lemma lem8026016 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term5 _141927 _141928 _141929 s t x) = (term6 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term5 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8026017 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term6 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8026016 _141927 _141928 _141929 x s t) (@lem8026015 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8026018 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term7 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8026017 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8026019 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x s t y) = ((term8 _141927 _141928 _141929 x y s t) = (term9 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term7 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8026021 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8026022 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem8026023 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem8026022 A s) (@lem8026021 A s)). Qed.
Lemma lem8026024 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (@lem8026023 A s t). Qed.
Lemma lem8026025 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = ((s = t) = (term13 A s t)).
Proof. exact (eq_refl (term12 A s t)). Qed.
Lemma lem8026030 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term13 A s t).
Proof. exact (EQ_MP (@lem8026025 A s t) (@lem8026024 A s t)). Qed.
Lemma lem8026031 {A M N : Type'} (s : type16 A M N) (t : type16 A M N) : (s = t) = (term14 A M N s t).
Proof. exact (@lem8026030 (type2 A M N) s t). Qed.
Lemma lem8026032 {A M N : Type'} : ((@PCROSS A M N (@UNIV (cart A M)) (@UNIV (cart A N))) = (@UNIV (cart A (finite_sum M N)))) = (term15 A M N).
Proof. exact (@lem8026031 A M N (@PCROSS A M N (@UNIV (cart A M)) (@UNIV (cart A N))) (@UNIV (cart A (finite_sum M N)))). Qed.
Lemma lem8026038 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term16 _140454 _140455 _140456 P) = (term17 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8026039 {A M N : Type'} (P : type16 A M N) : (term16 A M N P) = (term17 A M N P).
Proof. exact (@lem8026038 A M N P). Qed.
Lemma lem8026040 {A M N : Type'} : (term18 A M N) = (term19 A M N).
Proof. exact (@lem8026039 A M N (term20 A M N)). Qed.
Lemma lem8026041 {A M N : Type'} (x : type2 A M N) : (term21 A M N x) = ((term22 A M N x) = (@IN (cart A (finite_sum M N)) x (@UNIV (cart A (finite_sum M N))))).
Proof. exact (eq_refl (term21 A M N x)). Qed.
Lemma lem8026042 {A M N : Type'} : (term23 A M N) = (term20 A M N).
Proof. exact (fun_ext (fun x : type2 A M N => @lem8026041 A M N x)). Qed.
Lemma lem8026043 {A M N : Type'} : (@all (cart A (finite_sum M N))) = (@all (cart A (finite_sum M N))).
Proof. exact (eq_refl (@all (cart A (finite_sum M N)))). Qed.
Lemma lem8026044 {A M N : Type'} : (term18 A M N) = (term15 A M N).
Proof. exact (MK_COMB (@lem8026043 A M N) (@lem8026042 A M N)). Qed.
Lemma lem8026045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8026046 {A M N : Type'} : (term24 A M N) = (term25 A M N).
Proof. exact (MK_COMB (@lem8026045) (@lem8026044 A M N)). Qed.
Lemma lem8026047 {A M N : Type'} (x : cart A M) (y : cart A N) : (term26 A M N x y) = ((term27 A M N x y) = (term28 A M N x y)).
Proof. exact (eq_refl (term26 A M N x y)). Qed.
Lemma lem8026048 {A M N : Type'} (x : cart A M) : (term29 A M N x) = (term30 A M N x).
Proof. exact (fun_ext (fun y : cart A N => @lem8026047 A M N x y)). Qed.
Lemma lem8026049 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026050 {A M N : Type'} (x : cart A M) : (term31 A M N x) = (term32 A M N x).
Proof. exact (MK_COMB (@lem8026049 A N) (@lem8026048 A M N x)). Qed.
Lemma lem8026051 {A M N : Type'} : (term33 A M N) = (term34 A M N).
Proof. exact (fun_ext (fun x : cart A M => @lem8026050 A M N x)). Qed.
Lemma lem8026052 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026053 {A M N : Type'} : (term19 A M N) = (term35 A M N).
Proof. exact (MK_COMB (@lem8026052 A M) (@lem8026051 A M N)). Qed.
Lemma lem8026054 {A M N : Type'} : ((term18 A M N) = (term19 A M N)) = ((term15 A M N) = (term35 A M N)).
Proof. exact (MK_COMB (@lem8026046 A M N) (@lem8026053 A M N)). Qed.
Lemma lem8026055 {A M N : Type'} : (term15 A M N) = (term35 A M N).
Proof. exact (EQ_MP (@lem8026054 A M N) (@lem8026040 A M N)). Qed.
Lemma lem8026062 {A M N : Type'} : ((@PCROSS A M N (@UNIV (cart A M)) (@UNIV (cart A N))) = (@UNIV (cart A (finite_sum M N)))) = (term35 A M N).
Proof. exact (TRANS (@lem8026032 A M N) (@lem8026055 A M N)). Qed.
Lemma lem8026074 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term8 _141927 _141928 _141929 x y s t) = (term9 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8026019 _141927 _141928 _141929 x s y t) (@lem8026018 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8026075 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term8 A M N x y s t) = (term9 A M N x s y t).
Proof. exact (@lem8026074 A M N x s y t). Qed.
Lemma lem8026076 {A M N : Type'} (x : cart A M) (y : cart A N) : (term27 A M N x y) = (term36 A M N x y).
Proof. exact (@lem8026075 A M N x (@UNIV (cart A M)) y (@UNIV (cart A N))). Qed.
Lemma lem8026080 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem8026007 A x) (@lem8026006 A x)). Qed.
Lemma lem8026081 {A M : Type'} (x : cart A M) : (@IN (cart A M) x (@UNIV (cart A M))) = True.
Proof. exact (@lem8026080 (cart A M) x). Qed.
Lemma lem8026082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8026083 {A M : Type'} (x : cart A M) : (term37 A M x) = (and True).
Proof. exact (MK_COMB (@lem8026082) (@lem8026081 A M x)). Qed.
Lemma lem8026085 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem8026007 A x) (@lem8026006 A x)). Qed.
Lemma lem8026086 {A N : Type'} (x : cart A N) : (@IN (cart A N) x (@UNIV (cart A N))) = True.
Proof. exact (@lem8026085 (cart A N) x). Qed.
Lemma lem8026087 {A N : Type'} (y : cart A N) : (@IN (cart A N) y (@UNIV (cart A N))) = True.
Proof. exact (@lem8026086 A N y). Qed.
Lemma lem8026088 {A M N : Type'} (x : cart A M) (y : cart A N) : (term36 A M N x y) = (True /\ True).
Proof. exact (MK_COMB (@lem8026083 A M x) (@lem8026087 A N y)). Qed.
Lemma lem8026090 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8026091 : (True /\ True) = True.
Proof. exact (@lem8026090 True). Qed.
Lemma lem8026092 {A M N : Type'} (x : cart A M) (y : cart A N) : (term36 A M N x y) = True.
Proof. exact (TRANS (@lem8026088 A M N x y) (@lem8026091)). Qed.
Lemma lem8026093 {A M N : Type'} (x : cart A M) (y : cart A N) : (term27 A M N x y) = True.
Proof. exact (TRANS (@lem8026076 A M N x y) (@lem8026092 A M N x y)). Qed.
Lemma lem8026094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8026095 {A M N : Type'} (x : cart A M) (y : cart A N) : (term38 A M N x y) = (@eq Prop True).
Proof. exact (MK_COMB (@lem8026094) (@lem8026093 A M N x y)). Qed.
Lemma lem8026097 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem8026007 A x) (@lem8026006 A x)). Qed.
Lemma lem8026098 {A M N : Type'} (x : type2 A M N) : (@IN (cart A (finite_sum M N)) x (@UNIV (cart A (finite_sum M N)))) = True.
Proof. exact (@lem8026097 (type2 A M N) x). Qed.
Lemma lem8026099 {A M N : Type'} (x : cart A M) (y : cart A N) : (term28 A M N x y) = True.
Proof. exact (@lem8026098 A M N (@pastecart A M N x y)). Qed.
Lemma lem8026100 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term27 A M N x y) = (term28 A M N x y)) = (True = True).
Proof. exact (MK_COMB (@lem8026095 A M N x y) (@lem8026099 A M N x y)). Qed.
Lemma lem8026102 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem8026103 : (True = True) = True.
Proof. exact (@lem8026102 True). Qed.
Lemma lem8026104 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term27 A M N x y) = (term28 A M N x y)) = True.
Proof. exact (TRANS (@lem8026100 A M N x y) (@lem8026103)). Qed.
Lemma lem8026105 {A M N : Type'} (x : cart A M) : (term30 A M N x) = (term39 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem8026104 A M N x y)). Qed.
Lemma lem8026106 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8026107 {A M N : Type'} (x : cart A M) : (term32 A M N x) = (term40 A N).
Proof. exact (MK_COMB (@lem8026106 A N) (@lem8026105 A M N x)). Qed.
Lemma lem8026109 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8026110 {A N : Type'} (t : Prop) : (term42 A N t) = t.
Proof. exact (@lem8026109 (cart A N) t). Qed.
Lemma lem8026111 {A N : Type'} : (term40 A N) = True.
Proof. exact (@lem8026110 A N True). Qed.
Lemma lem8026112 {A M N : Type'} (x : cart A M) : (term32 A M N x) = True.
Proof. exact (TRANS (@lem8026107 A M N x) (@lem8026111 A N)). Qed.
Lemma lem8026113 {A M N : Type'} : (term34 A M N) = (term39 A M).
Proof. exact (fun_ext (fun x : cart A M => @lem8026112 A M N x)). Qed.
Lemma lem8026114 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8026115 {A M N : Type'} : (term35 A M N) = (term40 A M).
Proof. exact (MK_COMB (@lem8026114 A M) (@lem8026113 A M N)). Qed.
Lemma lem8026117 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8026118 {A M : Type'} (t : Prop) : (term42 A M t) = t.
Proof. exact (@lem8026117 (cart A M) t). Qed.
Lemma lem8026119 {A M : Type'} : (term40 A M) = True.
Proof. exact (@lem8026118 A M True). Qed.
Lemma lem8026120 {A M N : Type'} : (term35 A M N) = True.
Proof. exact (TRANS (@lem8026115 A M N) (@lem8026119 A M)). Qed.
Lemma lem8026121 {A M N : Type'} : ((@PCROSS A M N (@UNIV (cart A M)) (@UNIV (cart A N))) = (@UNIV (cart A (finite_sum M N)))) = True.
Proof. exact (TRANS (@lem8026062 A M N) (@lem8026120 A M N)). Qed.
Lemma lem8026122 {A M N : Type'} : True = ((@PCROSS A M N (@UNIV (cart A M)) (@UNIV (cart A N))) = (@UNIV (cart A (finite_sum M N)))).
Proof. exact (SYM (@lem8026121 A M N)). Qed.
Lemma lem8026123 {A M N : Type'} : (@PCROSS A M N (@UNIV (cart A M)) (@UNIV (cart A N))) = (@UNIV (cart A (finite_sum M N))).
Proof. exact (EQ_MP (@lem8026122 A M N) (@lem0)). Qed.
