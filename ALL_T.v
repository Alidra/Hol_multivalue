Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_T_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1124077 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1124078 {_26461 : Type'} (P : type1143 _26461) : term0 _26461 P.
Proof. exact (@lem1124077 _26461 P). Qed.
Lemma lem1124079 {_26461 : Type'} : term1 _26461.
Proof. exact (@lem1124078 _26461 (term2 _26461)). Qed.
Lemma lem1124080 {_26461 : Type'} : (term3 _26461) = (term4 _26461).
Proof. exact (eq_refl (term3 _26461)). Qed.
Lemma lem1124081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1124082 {_26461 : Type'} : (term5 _26461) = (term6 _26461).
Proof. exact (MK_COMB (@lem1124081) (@lem1124080 _26461)). Qed.
Lemma lem1124083 {_26461 : Type'} (t : list _26461) : (term7 _26461 t) = (term8 _26461 t).
Proof. exact (eq_refl (term7 _26461 t)). Qed.
Lemma lem1124084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124085 {_26461 : Type'} (t : list _26461) : (term9 _26461 t) = (term10 _26461 t).
Proof. exact (MK_COMB (@lem1124084) (@lem1124083 _26461 t)). Qed.
Lemma lem1124086 {_26461 : Type'} (h : _26461) (t : list _26461) : (term11 _26461 h t) = (term12 _26461 h t).
Proof. exact (eq_refl (term11 _26461 h t)). Qed.
Lemma lem1124087 {_26461 : Type'} (h : _26461) (t : list _26461) : (term13 _26461 h t) = (term14 _26461 h t).
Proof. exact (MK_COMB (@lem1124085 _26461 t) (@lem1124086 _26461 h t)). Qed.
Lemma lem1124088 {_26461 : Type'} (h : _26461) : (term15 _26461 h) = (term16 _26461 h).
Proof. exact (fun_ext (fun t : list _26461 => @lem1124087 _26461 h t)). Qed.
Lemma lem1124089 {_26461 : Type'} : (@all (list _26461)) = (@all (list _26461)).
Proof. exact (eq_refl (@all (list _26461))). Qed.
Lemma lem1124090 {_26461 : Type'} (h : _26461) : (term17 _26461 h) = (term18 _26461 h).
Proof. exact (MK_COMB (@lem1124089 _26461) (@lem1124088 _26461 h)). Qed.
Lemma lem1124091 {_26461 : Type'} : (term19 _26461) = (term20 _26461).
Proof. exact (fun_ext (fun h : _26461 => @lem1124090 _26461 h)). Qed.
Lemma lem1124092 {_26461 : Type'} : (@all _26461) = (@all _26461).
Proof. exact (eq_refl (@all _26461)). Qed.
Lemma lem1124093 {_26461 : Type'} : (term21 _26461) = (term22 _26461).
Proof. exact (MK_COMB (@lem1124092 _26461) (@lem1124091 _26461)). Qed.
Lemma lem1124094 {_26461 : Type'} : (term23 _26461) = (term24 _26461).
Proof. exact (MK_COMB (@lem1124082 _26461) (@lem1124093 _26461)). Qed.
Lemma lem1124095 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124096 {_26461 : Type'} : (term25 _26461) = (term26 _26461).
Proof. exact (MK_COMB (@lem1124095) (@lem1124094 _26461)). Qed.
Lemma lem1124097 {_26461 : Type'} (l : list _26461) : (term7 _26461 l) = (term8 _26461 l).
Proof. exact (eq_refl (term7 _26461 l)). Qed.
Lemma lem1124098 {_26461 : Type'} : (term27 _26461) = (term2 _26461).
Proof. exact (fun_ext (fun l : list _26461 => @lem1124097 _26461 l)). Qed.
Lemma lem1124099 {_26461 : Type'} : (@all (list _26461)) = (@all (list _26461)).
Proof. exact (eq_refl (@all (list _26461))). Qed.
Lemma lem1124100 {_26461 : Type'} : (term28 _26461) = (term29 _26461).
Proof. exact (MK_COMB (@lem1124099 _26461) (@lem1124098 _26461)). Qed.
Lemma lem1124101 {_26461 : Type'} : (term1 _26461) = (term30 _26461).
Proof. exact (MK_COMB (@lem1124096 _26461) (@lem1124100 _26461)). Qed.
Lemma lem1124102 {_26461 : Type'} : term30 _26461.
Proof. exact (EQ_MP (@lem1124101 _26461) (@lem1124079 _26461)). Qed.
Lemma lem1124103 {_26461 : Type'} (t : list _26461) (h1 : term8 _26461 t) : term8 _26461 t.
Proof. exact (h1). Qed.
Lemma lem1124107 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1124108 {_26461 : Type'} (P : _26461 -> Prop) : (@List.Forall _26461 P (@nil _26461)) = True.
Proof. exact (@lem1124107 _26461 P). Qed.
Lemma lem1124109 {_26461 : Type'} : (term4 _26461) = True.
Proof. exact (@lem1124108 _26461 (term31 _26461)). Qed.
Lemma lem1124110 {_26461 : Type'} : True = (term4 _26461).
Proof. exact (SYM (@lem1124109 _26461)). Qed.
Lemma lem1124111 {_26461 : Type'} : term4 _26461.
Proof. exact (EQ_MP (@lem1124110 _26461) (@lem0)). Qed.
Lemma lem1124114 {_26461 : Type'} (t : list _26461) : (term8 _26461 t) = ((term8 _26461 t) = True).
Proof. exact (@lem7 (term8 _26461 t)). Qed.
Lemma lem1124117 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term32 _25307 P h t) = (term33 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1124118 {_26461 : Type'} (h : _26461) (P : _26461 -> Prop) (t : list _26461) : (term32 _26461 P h t) = (term33 _26461 h P t).
Proof. exact (@lem1124117 _26461 h P t). Qed.
Lemma lem1124119 {_26461 : Type'} (h : _26461) (t : list _26461) : (term12 _26461 h t) = (term34 _26461 h t).
Proof. exact (@lem1124118 _26461 h (term31 _26461) t). Qed.
Lemma lem1124123 {A B : Type'} (f : A -> B) (y : A) : (term35 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1124124 {_26461 : Type'} (f : _26461 -> Prop) (y : _26461) : (term36 _26461 f y) = (f y).
Proof. exact (@lem1124123 _26461 Prop f y). Qed.
Lemma lem1124125 {_26461 : Type'} (h : _26461) : (term37 _26461 h) = (term38 _26461 h).
Proof. exact (@lem1124124 _26461 (term31 _26461) h). Qed.
Lemma lem1124126 {_26461 : Type'} (x : _26461) : (term38 _26461 x) = True.
Proof. exact (eq_refl (term38 _26461 x)). Qed.
Lemma lem1124127 {_26461 : Type'} : (term39 _26461) = (term31 _26461).
Proof. exact (fun_ext (fun x : _26461 => @lem1124126 _26461 x)). Qed.
Lemma lem1124128 {_26461 : Type'} (h : _26461) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1124129 {_26461 : Type'} (h : _26461) : (term37 _26461 h) = (term38 _26461 h).
Proof. exact (MK_COMB (@lem1124127 _26461) (@lem1124128 _26461 h)). Qed.
Lemma lem1124130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1124131 {_26461 : Type'} (h : _26461) : (term40 _26461 h) = (term41 _26461 h).
Proof. exact (MK_COMB (@lem1124130) (@lem1124129 _26461 h)). Qed.
Lemma lem1124132 {_26461 : Type'} (h : _26461) : (term38 _26461 h) = True.
Proof. exact (eq_refl (term38 _26461 h)). Qed.
Lemma lem1124133 {_26461 : Type'} (h : _26461) : ((term37 _26461 h) = (term38 _26461 h)) = ((term38 _26461 h) = True).
Proof. exact (MK_COMB (@lem1124131 _26461 h) (@lem1124132 _26461 h)). Qed.
Lemma lem1124134 {_26461 : Type'} (h : _26461) : (term38 _26461 h) = True.
Proof. exact (EQ_MP (@lem1124133 _26461 h) (@lem1124125 _26461 h)). Qed.
Lemma lem1124135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1124136 {_26461 : Type'} (h : _26461) : (term42 _26461 h) = (and True).
Proof. exact (MK_COMB (@lem1124135) (@lem1124134 _26461 h)). Qed.
Lemma lem1124138 {_26461 : Type'} (t : list _26461) (h1 : term8 _26461 t) : (term8 _26461 t) = True.
Proof. exact (EQ_MP (@lem1124114 _26461 t) (@lem1124103 _26461 t h1)). Qed.
Lemma lem1124139 {_26461 : Type'} (t : list _26461) (h1 : term8 _26461 t) : (term8 _26461 t) = True.
Proof. exact (@lem1124138 _26461 t h1). Qed.
Lemma lem1124140 {_26461 : Type'} (h : _26461) (t : list _26461) (h1 : term8 _26461 t) : (term34 _26461 h t) = (True /\ True).
Proof. exact (MK_COMB (@lem1124136 _26461 h) (@lem1124139 _26461 t h1)). Qed.
Lemma lem1124142 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1124143 : (True /\ True) = True.
Proof. exact (@lem1124142 True). Qed.
Lemma lem1124144 {_26461 : Type'} (h : _26461) (t : list _26461) (h1 : term8 _26461 t) : (term34 _26461 h t) = True.
Proof. exact (TRANS (@lem1124140 _26461 h t h1) (@lem1124143)). Qed.
Lemma lem1124145 {_26461 : Type'} (h : _26461) (t : list _26461) (h1 : term8 _26461 t) : (term12 _26461 h t) = True.
Proof. exact (TRANS (@lem1124119 _26461 h t) (@lem1124144 _26461 h t h1)). Qed.
Lemma lem1124146 {_26461 : Type'} (h : _26461) (t : list _26461) (h1 : term8 _26461 t) : True = (term12 _26461 h t).
Proof. exact (SYM (@lem1124145 _26461 h t h1)). Qed.
Lemma lem1124147 {_26461 : Type'} (h : _26461) (t : list _26461) (h1 : term8 _26461 t) : term12 _26461 h t.
Proof. exact (EQ_MP (@lem1124146 _26461 h t h1) (@lem0)). Qed.
Lemma lem1124148 {_26461 : Type'} (h : _26461) (t : list _26461) : term14 _26461 h t.
Proof. exact (fun h0 : term8 _26461 t => @lem1124147 _26461 h t h0). Qed.
Lemma lem1124153 {_26461 : Type'} (h : _26461) : term18 _26461 h.
Proof. exact (fun t : list _26461 => @lem1124148 _26461 h t). Qed.
Lemma lem1124158 {_26461 : Type'} : term22 _26461.
Proof. exact (fun h : _26461 => @lem1124153 _26461 h). Qed.
Lemma lem1124159 {_26461 : Type'} : term24 _26461.
Proof. exact (conj (@lem1124111 _26461) (@lem1124158 _26461)). Qed.
Lemma lem1124160 {_26461 : Type'} : term29 _26461.
Proof. exact (@lem1124102 _26461 (@lem1124159 _26461)). Qed.
