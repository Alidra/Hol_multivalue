Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_EQ_CONS_term_abbrevs.
Require Import CONS_11_spec.
Require Import DISJ_ASSOC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18394_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm82_spec.
Lemma lem1117067 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1117068 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1117069 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1117068 t1) (@lem1117067 t1)). Qed.
Lemma lem1117070 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1117069 t1 t2). Qed.
Lemma lem1117071 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1117072 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1117071 t1 t2) (@lem1117070 t1 t2)). Qed.
Lemma lem1117073 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1117072 t1 t2 t3). Qed.
Lemma lem1117074 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1117075 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1117074 t1 t2 t3) (@lem1117073 t1 t2 t3)). Qed.
Lemma lem1117076 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1117075 t1 t2 t3)). Qed.
Lemma lem1117077 {A : Type'} (h : A) : term7 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1117078 {A : Type'} (h : A) : (term7 A h) = (term8 A h).
Proof. exact (eq_refl (term7 A h)). Qed.
Lemma lem1117079 {A : Type'} (h : A) : term8 A h.
Proof. exact (EQ_MP (@lem1117078 A h) (@lem1117077 A h)). Qed.
Lemma lem1117080 {A : Type'} (h : A) (t : list A) : term9 A h t.
Proof. exact (@lem1117079 A h t). Qed.
Lemma lem1117081 {A : Type'} (h : A) (t : list A) : (term9 A h t) = (term10 A h t).
Proof. exact (eq_refl (term9 A h t)). Qed.
Lemma lem1117082 {A : Type'} (h : A) (t : list A) : term10 A h t.
Proof. exact (EQ_MP (@lem1117081 A h t) (@lem1117080 A h t)). Qed.
Lemma lem1117086 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@cons A h t) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1117087 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@nil A) = (@cons A h t).
Proof. exact (SYM (@lem1117086 A h t h1)). Qed.
Lemma lem1117088 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@nil A) = (@cons A h t).
Proof. exact (h1). Qed.
Lemma lem1117089 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@cons A h t) = (@nil A).
Proof. exact (SYM (@lem1117088 A h t h1)). Qed.
Lemma lem1117090 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = ((@nil A) = (@cons A h t)).
Proof. exact (prop_ext (fun h1 : (@cons A h t) = (@nil A) => @lem1117087 A h t h1) (fun h1 : (@nil A) = (@cons A h t) => @lem1117089 A h t h1)). Qed.
Lemma lem1117091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1117092 {A : Type'} (h : A) (t : list A) : (term10 A h t) = (term11 A h t).
Proof. exact (MK_COMB (@lem1117091) (@lem1117090 A h t)). Qed.
Lemma lem1117093 {A : Type'} (h : A) (t : list A) : term11 A h t.
Proof. exact (EQ_MP (@lem1117092 A h t) (@lem1117082 A h t)). Qed.
Lemma lem1117094 {A : Type'} (h : A) (t : list A) : term12 A h t.
Proof. exact (@lem82 ((@nil A) = (@cons A h t))). Qed.
Lemma lem1117096 (n : nat) : term13 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1117097 (n : nat) : (term13 n) = (term14 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem1117098 (n : nat) : term14 n.
Proof. exact (EQ_MP (@lem1117097 n) (@lem1117096 n)). Qed.
Lemma lem1117102 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1117103 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1117102 n h1)). Qed.
Lemma lem1117104 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1117105 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1117104 n h1)). Qed.
Lemma lem1117106 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem1117103 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem1117105 n h1)). Qed.
Lemma lem1117107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1117108 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem1117107) (@lem1117106 n)). Qed.
Lemma lem1117109 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem1117108 n) (@lem1117098 n)). Qed.
Lemma lem1117110 (n : nat) : term16 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem1117112 {A : Type'} : term17 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1117113 {A : Type'} (h : A) : term18 A h.
Proof. exact (@lem1117112 A h). Qed.
Lemma lem1117114 {A : Type'} (h : A) : (term18 A h) = (term19 A h).
Proof. exact (eq_refl (term18 A h)). Qed.
Lemma lem1117115 {A : Type'} (h : A) : term19 A h.
Proof. exact (EQ_MP (@lem1117114 A h) (@lem1117113 A h)). Qed.
Lemma lem1117116 {A : Type'} (h : A) (t : list A) : term20 A h t.
Proof. exact (@lem1117115 A h t). Qed.
Lemma lem1117117 {A : Type'} (h : A) (t : list A) : (term20 A h t) = ((term21 A h t) = (term22 A t)).
Proof. exact (eq_refl (term20 A h t)). Qed.
Lemma lem1117121 {A : Type'} (P : type1143 A) : term23 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1117122 {_26221 : Type'} (P : type1143 _26221) : term23 _26221 P.
Proof. exact (@lem1117121 _26221 P). Qed.
Lemma lem1117123 {_26221 : Type'} : term24 _26221.
Proof. exact (@lem1117122 _26221 (term25 _26221)). Qed.
Lemma lem1117124 {_26221 : Type'} : (term26 _26221) = (term27 _26221).
Proof. exact (eq_refl (term26 _26221)). Qed.
Lemma lem1117125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1117126 {_26221 : Type'} : (term28 _26221) = (term29 _26221).
Proof. exact (MK_COMB (@lem1117125) (@lem1117124 _26221)). Qed.
Lemma lem1117127 {_26221 : Type'} (t : list _26221) : (term30 _26221 t) = (term31 _26221 t).
Proof. exact (eq_refl (term30 _26221 t)). Qed.
Lemma lem1117128 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1117129 {_26221 : Type'} (t : list _26221) : (term32 _26221 t) = (term33 _26221 t).
Proof. exact (MK_COMB (@lem1117128) (@lem1117127 _26221 t)). Qed.
Lemma lem1117130 {_26221 : Type'} (h : _26221) (t : list _26221) : (term34 _26221 h t) = (term35 _26221 h t).
Proof. exact (eq_refl (term34 _26221 h t)). Qed.
Lemma lem1117131 {_26221 : Type'} (h : _26221) (t : list _26221) : (term36 _26221 h t) = (term37 _26221 h t).
Proof. exact (MK_COMB (@lem1117129 _26221 t) (@lem1117130 _26221 h t)). Qed.
Lemma lem1117132 {_26221 : Type'} (h : _26221) : (term38 _26221 h) = (term39 _26221 h).
Proof. exact (fun_ext (fun t : list _26221 => @lem1117131 _26221 h t)). Qed.
Lemma lem1117133 {_26221 : Type'} : (@all (list _26221)) = (@all (list _26221)).
Proof. exact (eq_refl (@all (list _26221))). Qed.
Lemma lem1117134 {_26221 : Type'} (h : _26221) : (term40 _26221 h) = (term41 _26221 h).
Proof. exact (MK_COMB (@lem1117133 _26221) (@lem1117132 _26221 h)). Qed.
Lemma lem1117135 {_26221 : Type'} : (term42 _26221) = (term43 _26221).
Proof. exact (fun_ext (fun h : _26221 => @lem1117134 _26221 h)). Qed.
Lemma lem1117136 {_26221 : Type'} : (@all _26221) = (@all _26221).
Proof. exact (eq_refl (@all _26221)). Qed.
Lemma lem1117137 {_26221 : Type'} : (term44 _26221) = (term45 _26221).
Proof. exact (MK_COMB (@lem1117136 _26221) (@lem1117135 _26221)). Qed.
Lemma lem1117138 {_26221 : Type'} : (term46 _26221) = (term47 _26221).
Proof. exact (MK_COMB (@lem1117126 _26221) (@lem1117137 _26221)). Qed.
Lemma lem1117139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1117140 {_26221 : Type'} : (term48 _26221) = (term49 _26221).
Proof. exact (MK_COMB (@lem1117139) (@lem1117138 _26221)). Qed.
Lemma lem1117141 {_26221 : Type'} (l : list _26221) : (term30 _26221 l) = (term31 _26221 l).
Proof. exact (eq_refl (term30 _26221 l)). Qed.
Lemma lem1117142 {_26221 : Type'} : (term50 _26221) = (term25 _26221).
Proof. exact (fun_ext (fun l : list _26221 => @lem1117141 _26221 l)). Qed.
Lemma lem1117143 {_26221 : Type'} : (@all (list _26221)) = (@all (list _26221)).
Proof. exact (eq_refl (@all (list _26221))). Qed.
Lemma lem1117144 {_26221 : Type'} : (term51 _26221) = (term52 _26221).
Proof. exact (MK_COMB (@lem1117143 _26221) (@lem1117142 _26221)). Qed.
Lemma lem1117145 {_26221 : Type'} : (term24 _26221) = (term53 _26221).
Proof. exact (MK_COMB (@lem1117140 _26221) (@lem1117144 _26221)). Qed.
Lemma lem1117146 {_26221 : Type'} : term53 _26221.
Proof. exact (EQ_MP (@lem1117145 _26221) (@lem1117123 _26221)). Qed.
Lemma lem1117157 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1117158 {_26221 : Type'} : (@List.length _26221 (@nil _26221)) = (NUMERAL 0).
Proof. exact (@lem1117157 _26221). Qed.
Lemma lem1117159 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1117160 {_26221 : Type'} : (term54 _26221) = term55.
Proof. exact (MK_COMB (@lem1117159) (@lem1117158 _26221)). Qed.
Lemma lem1117161 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1117162 {_26221 : Type'} (n : nat) : ((@List.length _26221 (@nil _26221)) = (S n)) = ((NUMERAL 0) = (S n)).
Proof. exact (MK_COMB (@lem1117160 _26221) (@lem1117161 n)). Qed.
Lemma lem1117164 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem1117110 n (@lem1117109 n)). Qed.
Lemma lem1117165 {_26221 : Type'} (n : nat) : ((@List.length _26221 (@nil _26221)) = (S n)) = False.
Proof. exact (TRANS (@lem1117162 _26221 n) (@lem1117164 n)). Qed.
Lemma lem1117166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117167 {_26221 : Type'} (n : nat) : (term56 _26221 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1117166) (@lem1117165 _26221 n)). Qed.
Lemma lem1117179 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1117094 A h t (@lem1117093 A h t)). Qed.
Lemma lem1117180 {_26221 : Type'} (h : _26221) (t : list _26221) : ((@nil _26221) = (@cons _26221 h t)) = False.
Proof. exact (@lem1117179 _26221 h t). Qed.
Lemma lem1117181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1117182 {_26221 : Type'} (h : _26221) (t : list _26221) : (term57 _26221 h t) = (and False).
Proof. exact (MK_COMB (@lem1117181) (@lem1117180 _26221 h t)). Qed.
Lemma lem1117185 {_26221 : Type'} (t : list _26221) (n : nat) : ((@List.length _26221 t) = n) = ((@List.length _26221 t) = n).
Proof. exact (eq_refl ((@List.length _26221 t) = n)). Qed.
Lemma lem1117186 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term58 _26221 h t n) = (term59 _26221 t n).
Proof. exact (MK_COMB (@lem1117182 _26221 h t) (@lem1117185 _26221 t n)). Qed.
Lemma lem1117188 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1117189 {_26221 : Type'} (t : list _26221) (n : nat) : (term59 _26221 t n) = False.
Proof. exact (@lem1117188 ((@List.length _26221 t) = n)). Qed.
Lemma lem1117190 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term58 _26221 h t n) = False.
Proof. exact (TRANS (@lem1117186 _26221 h t n) (@lem1117189 _26221 t n)). Qed.
Lemma lem1117191 {_26221 : Type'} (h : _26221) (n : nat) : (term60 _26221 h n) = (term61 _26221).
Proof. exact (fun_ext (fun t : list _26221 => @lem1117190 _26221 h t n)). Qed.
Lemma lem1117192 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117193 {_26221 : Type'} (h : _26221) (n : nat) : (term62 _26221 h n) = (term63 _26221).
Proof. exact (MK_COMB (@lem1117192 _26221) (@lem1117191 _26221 h n)). Qed.
Lemma lem1117195 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1117196 {_26221 : Type'} (t : Prop) : (term65 _26221 t) = t.
Proof. exact (@lem1117195 (list _26221) t). Qed.
Lemma lem1117197 {_26221 : Type'} : (term63 _26221) = False.
Proof. exact (@lem1117196 _26221 False). Qed.
Lemma lem1117198 {_26221 : Type'} (h : _26221) (n : nat) : (term62 _26221 h n) = False.
Proof. exact (TRANS (@lem1117193 _26221 h n) (@lem1117197 _26221)). Qed.
Lemma lem1117199 {_26221 : Type'} (n : nat) : (term66 _26221 n) = (term67 _26221).
Proof. exact (fun_ext (fun h : _26221 => @lem1117198 _26221 h n)). Qed.
Lemma lem1117200 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117201 {_26221 : Type'} (n : nat) : (term68 _26221 n) = (term69 _26221).
Proof. exact (MK_COMB (@lem1117200 _26221) (@lem1117199 _26221 n)). Qed.
Lemma lem1117203 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1117204 {_26221 : Type'} (t : Prop) : (term64 _26221 t) = t.
Proof. exact (@lem1117203 _26221 t). Qed.
Lemma lem1117205 {_26221 : Type'} : (term69 _26221) = False.
Proof. exact (@lem1117204 _26221 False). Qed.
Lemma lem1117206 {_26221 : Type'} (n : nat) : (term68 _26221 n) = False.
Proof. exact (TRANS (@lem1117201 _26221 n) (@lem1117205 _26221)). Qed.
Lemma lem1117207 {_26221 : Type'} (n : nat) : (((@List.length _26221 (@nil _26221)) = (S n)) = (term68 _26221 n)) = (False = False).
Proof. exact (MK_COMB (@lem1117167 _26221 n) (@lem1117206 _26221 n)). Qed.
Lemma lem1117209 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1117210 : (False = False) = (~ False).
Proof. exact (@lem1117209 False). Qed.
Lemma lem1117212 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1117213 : (False = False) = True.
Proof. exact (TRANS (@lem1117210) (@lem1117212)). Qed.
Lemma lem1117214 {_26221 : Type'} (n : nat) : (((@List.length _26221 (@nil _26221)) = (S n)) = (term68 _26221 n)) = True.
Proof. exact (TRANS (@lem1117207 _26221 n) (@lem1117213)). Qed.
Lemma lem1117215 {_26221 : Type'} : (term70 _26221) = term71.
Proof. exact (fun_ext (fun n : nat => @lem1117214 _26221 n)). Qed.
Lemma lem1117216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1117217 {_26221 : Type'} : (term27 _26221) = term72.
Proof. exact (MK_COMB (@lem1117216) (@lem1117215 _26221)). Qed.
Lemma lem1117219 {A : Type'} (t : Prop) : (term73 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1117220 (t : Prop) : (term74 t) = t.
Proof. exact (@lem1117219 nat t). Qed.
Lemma lem1117221 : term72 = True.
Proof. exact (@lem1117220 True). Qed.
Lemma lem1117222 {_26221 : Type'} : (term27 _26221) = True.
Proof. exact (TRANS (@lem1117217 _26221) (@lem1117221)). Qed.
Lemma lem1117223 {_26221 : Type'} : True = (term27 _26221).
Proof. exact (SYM (@lem1117222 _26221)). Qed.
Lemma lem1117224 {_26221 : Type'} : term27 _26221.
Proof. exact (EQ_MP (@lem1117223 _26221) (@lem0)). Qed.
Lemma lem1117234 {A : Type'} (h : A) (t : list A) : (term21 A h t) = (term22 A t).
Proof. exact (EQ_MP (@lem1117117 A h t) (@lem1117116 A h t)). Qed.
Lemma lem1117235 {_26221 : Type'} (h : _26221) (t : list _26221) : (term21 _26221 h t) = (term22 _26221 t).
Proof. exact (@lem1117234 _26221 h t). Qed.
Lemma lem1117236 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1117237 {_26221 : Type'} (h : _26221) (t : list _26221) : (term75 _26221 h t) = (term76 _26221 t).
Proof. exact (MK_COMB (@lem1117236) (@lem1117235 _26221 h t)). Qed.
Lemma lem1117238 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1117239 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : ((term21 _26221 h t) = (S n)) = ((term22 _26221 t) = (S n)).
Proof. exact (MK_COMB (@lem1117237 _26221 h t) (@lem1117238 n)). Qed.
Lemma lem1117242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117243 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term77 _26221 h t n) = (term78 _26221 t n).
Proof. exact (MK_COMB (@lem1117242) (@lem1117239 _26221 h t n)). Qed.
Lemma lem1117258 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term79 _26221 h t n) = (term79 _26221 h t n).
Proof. exact (eq_refl (term79 _26221 h t n)). Qed.
Lemma lem1117259 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (((term21 _26221 h t) = (S n)) = (term79 _26221 h t n)) = (((term22 _26221 t) = (S n)) = (term79 _26221 h t n)).
Proof. exact (MK_COMB (@lem1117243 _26221 h t n) (@lem1117258 _26221 h t n)). Qed.
Lemma lem1117262 {_26221 : Type'} (h : _26221) (t : list _26221) : (term80 _26221 h t) = (term81 _26221 h t).
Proof. exact (fun_ext (fun n : nat => @lem1117259 _26221 h t n)). Qed.
Lemma lem1117263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1117264 {_26221 : Type'} (h : _26221) (t : list _26221) : (term35 _26221 h t) = (term82 _26221 h t).
Proof. exact (MK_COMB (@lem1117263) (@lem1117262 _26221 h t)). Qed.
Lemma lem1117269 {_26221 : Type'} (h : _26221) (t : list _26221) : (term82 _26221 h t) = (term35 _26221 h t).
Proof. exact (SYM (@lem1117264 _26221 h t)). Qed.
Lemma lem1117270 {A : Type'} (h1' : A) : term83 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1117271 {A : Type'} (h1' : A) : (term83 A h1') = (term84 A h1').
Proof. exact (eq_refl (term83 A h1')). Qed.
Lemma lem1117272 {A : Type'} (h1' : A) : term84 A h1'.
Proof. exact (EQ_MP (@lem1117271 A h1') (@lem1117270 A h1')). Qed.
Lemma lem1117273 {A : Type'} (h1' : A) (h2' : A) : term85 A h1' h2'.
Proof. exact (@lem1117272 A h1' h2'). Qed.
Lemma lem1117274 {A : Type'} (h1' : A) (h2' : A) : (term85 A h1' h2') = (term86 A h1' h2').
Proof. exact (eq_refl (term85 A h1' h2')). Qed.
Lemma lem1117275 {A : Type'} (h1' : A) (h2' : A) : term86 A h1' h2'.
Proof. exact (EQ_MP (@lem1117274 A h1' h2') (@lem1117273 A h1' h2')). Qed.
Lemma lem1117276 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term87 A h1' h2' t1.
Proof. exact (@lem1117275 A h1' h2' t1). Qed.
Lemma lem1117277 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term87 A h1' h2' t1) = (term88 A h1' h2' t1).
Proof. exact (eq_refl (term87 A h1' h2' t1)). Qed.
Lemma lem1117278 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term88 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1117277 A h1' h2' t1) (@lem1117276 A h1' h2' t1)). Qed.
Lemma lem1117279 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term89 A h1' h2' t1 t2.
Proof. exact (@lem1117278 A h1' h2' t1 t2). Qed.
Lemma lem1117280 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term89 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term90 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term89 A h1' h2' t1 t2)). Qed.
Lemma lem1117282 (m : nat) : term91 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1117283 (m : nat) : (term91 m) = (term92 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem1117284 (m : nat) : term92 m.
Proof. exact (EQ_MP (@lem1117283 m) (@lem1117282 m)). Qed.
Lemma lem1117285 (m : nat) (n : nat) : term93 m n.
Proof. exact (@lem1117284 m n). Qed.
Lemma lem1117286 (m : nat) (n : nat) : (term93 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem1117298 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1117286 m n) (@lem1117285 m n)). Qed.
Lemma lem1117299 {_26221 : Type'} (t : list _26221) (n : nat) : ((term22 _26221 t) = (S n)) = ((@List.length _26221 t) = n).
Proof. exact (@lem1117298 (@List.length _26221 t) n). Qed.
Lemma lem1117302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117303 {_26221 : Type'} (t : list _26221) (n : nat) : (term78 _26221 t n) = (term94 _26221 t n).
Proof. exact (MK_COMB (@lem1117302) (@lem1117299 _26221 t n)). Qed.
Lemma lem1117315 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term90 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1117280 A h1' h2' t1 t2) (@lem1117279 A h1' h2' t1 t2)). Qed.
Lemma lem1117316 {_26221 : Type'} (h1' : _26221) (h2' : _26221) (t1 : list _26221) (t2 : list _26221) : ((@cons _26221 h1' t1) = (@cons _26221 h2' t2)) = (term90 _26221 h1' h2' t1 t2).
Proof. exact (@lem1117315 _26221 h1' h2' t1 t2). Qed.
Lemma lem1117317 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) : ((@cons _26221 h t) = (@cons _26221 h' t')) = (term90 _26221 h h' t t').
Proof. exact (@lem1117316 _26221 h h' t t'). Qed.
Lemma lem1117324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1117325 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) : (term95 _26221 h t h' t') = (term96 _26221 h h' t t').
Proof. exact (MK_COMB (@lem1117324) (@lem1117317 _26221 h h' t t')). Qed.
Lemma lem1117328 {_26221 : Type'} (t' : list _26221) (n : nat) : ((@List.length _26221 t') = n) = ((@List.length _26221 t') = n).
Proof. exact (eq_refl ((@List.length _26221 t') = n)). Qed.
Lemma lem1117329 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term97 _26221 h t h' t' n) = (term98 _26221 h h' t t' n).
Proof. exact (MK_COMB (@lem1117325 _26221 h h' t t') (@lem1117328 _26221 t' n)). Qed.
Lemma lem1117332 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term99 _26221 h t h' n) = (term100 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117329 _26221 h h' t t' n)). Qed.
Lemma lem1117333 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117334 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term101 _26221 h t h' n) = (term102 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117333 _26221) (@lem1117332 _26221 h h' t n)). Qed.
Lemma lem1117339 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term103 _26221 h t n) = (term104 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117334 _26221 h h' t n)). Qed.
Lemma lem1117340 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117341 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term79 _26221 h t n) = (term105 _26221 h t n).
Proof. exact (MK_COMB (@lem1117340 _26221) (@lem1117339 _26221 h t n)). Qed.
Lemma lem1117346 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (((term22 _26221 t) = (S n)) = (term79 _26221 h t n)) = (((@List.length _26221 t) = n) = (term105 _26221 h t n)).
Proof. exact (MK_COMB (@lem1117303 _26221 t n) (@lem1117341 _26221 h t n)). Qed.
Lemma lem1117349 {_26221 : Type'} (h : _26221) (t : list _26221) : (term81 _26221 h t) = (term106 _26221 h t).
Proof. exact (fun_ext (fun n : nat => @lem1117346 _26221 h t n)). Qed.
Lemma lem1117350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1117351 {_26221 : Type'} (h : _26221) (t : list _26221) : (term82 _26221 h t) = (term107 _26221 h t).
Proof. exact (MK_COMB (@lem1117350) (@lem1117349 _26221 h t)). Qed.
Lemma lem1117356 {_26221 : Type'} (h : _26221) (t : list _26221) : (term107 _26221 h t) = (term82 _26221 h t).
Proof. exact (SYM (@lem1117351 _26221 h t)). Qed.
Lemma lem1117358 (p : Prop) : p = (term108 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1117359 {_26221 : Type'} (h : _26221) (t : list _26221) : (term107 _26221 h t) = (term109 _26221 h t).
Proof. exact (@lem1117358 (term107 _26221 h t)). Qed.
Lemma lem1117360 {_26221 : Type'} (h : _26221) (t : list _26221) : (term109 _26221 h t) = (term107 _26221 h t).
Proof. exact (SYM (@lem1117359 _26221 h t)). Qed.
Lemma lem1117361 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term110 _26221 h t) : term110 _26221 h t.
Proof. exact (h1). Qed.
Lemma lem1117364 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term109 _26221 h t) : term109 _26221 h t.
Proof. exact (h1). Qed.
Lemma lem1117365 {_26221 : Type'} (h : _26221) (t : list _26221) : term111 _26221 h t.
Proof. exact (fun h0 : term109 _26221 h t => @lem1117364 _26221 h t h0). Qed.
Lemma lem1117366 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term111 _26221 h t) : term111 _26221 h t.
Proof. exact (h1). Qed.
Lemma lem1117367 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term109 _26221 h t) : term109 _26221 h t.
Proof. exact (h1). Qed.
Lemma lem1117368 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term109 _26221 h t) (h2 : term111 _26221 h t) : term109 _26221 h t.
Proof. exact (@lem1117366 _26221 h t h2 (@lem1117367 _26221 h t h1)). Qed.
Lemma lem1117369 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term109 _26221 h t) : term112 _26221 h t.
Proof. exact (fun h0 : term111 _26221 h t => @lem1117368 _26221 h t h1 h0). Qed.
Lemma lem1117370 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term111 _26221 h t) : term111 _26221 h t.
Proof. exact (h1). Qed.
Lemma lem1117371 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term109 _26221 h t) (h2 : term111 _26221 h t) : term109 _26221 h t.
Proof. exact (@lem1117369 _26221 h t h1 (@lem1117370 _26221 h t h2)). Qed.
Lemma lem1117372 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term111 _26221 h t) : term111 _26221 h t.
Proof. exact (fun h0 : term109 _26221 h t => @lem1117371 _26221 h t h0 h1). Qed.
Lemma lem1117373 {_26221 : Type'} (h : _26221) (t : list _26221) : term113 _26221 h t.
Proof. exact (fun h0 : term111 _26221 h t => @lem1117372 _26221 h t h0). Qed.
Lemma lem1117376 {_26221 : Type'} (h : _26221) (t : list _26221) : term111 _26221 h t.
Proof. exact (@lem1117373 _26221 h t (@lem1117365 _26221 h t)). Qed.
Lemma lem1117377 {_26221 : Type'} (h : _26221) (t : list _26221) : term111 _26221 h t.
Proof. exact (@lem1117376 _26221 h t). Qed.
Lemma lem1117387 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1117388 {_26221 : Type'} (h : _26221) (t : list _26221) : (term109 _26221 h t) = (term114 _26221 h t).
Proof. exact (@lem1117387 (term110 _26221 h t)). Qed.
Lemma lem1117390 (t : Prop) : (term115 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1117391 {_26221 : Type'} (h : _26221) (t : list _26221) : (term114 _26221 h t) = (term107 _26221 h t).
Proof. exact (@lem1117390 (term107 _26221 h t)). Qed.
Lemma lem1117396 {_26221 : Type'} (h : _26221) (t : list _26221) : (term109 _26221 h t) = (term107 _26221 h t).
Proof. exact (TRANS (@lem1117388 _26221 h t) (@lem1117391 _26221 h t)). Qed.
Lemma lem1117453 {_26221 : Type'} (t : list _26221) : (term116 _26221 t) = (term117 _26221 t).
Proof. exact (fun_ext (fun h : _26221 => @lem1117396 _26221 h t)). Qed.
Lemma lem1117454 {_26221 : Type'} : (@all _26221) = (@all _26221).
Proof. exact (eq_refl (@all _26221)). Qed.
Lemma lem1117455 {_26221 : Type'} (t : list _26221) : (term118 _26221 t) = (term119 _26221 t).
Proof. exact (MK_COMB (@lem1117454 _26221) (@lem1117453 _26221 t)). Qed.
Lemma lem1117460 {_26221 : Type'} : (term120 _26221) = (term121 _26221).
Proof. exact (fun_ext (fun t : list _26221 => @lem1117455 _26221 t)). Qed.
Lemma lem1117461 {_26221 : Type'} : (@all (list _26221)) = (@all (list _26221)).
Proof. exact (eq_refl (@all (list _26221))). Qed.
Lemma lem1117470 {_26221 : Type'} : (term122 _26221) = (term123 _26221).
Proof. exact (MK_COMB (@lem1117461 _26221) (@lem1117460 _26221)). Qed.
Lemma lem1117479 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term98 _26221 h h' t t' n) = (term98 _26221 h h' t t' n).
Proof. exact (eq_refl (term98 _26221 h h' t t' n)). Qed.
Lemma lem1117480 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term100 _26221 h h' t n) = (term100 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117479 _26221 h h' t t' n)). Qed.
Lemma lem1117481 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117482 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term102 _26221 h h' t n) = (term102 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117481 _26221) (@lem1117480 _26221 h h' t n)). Qed.
Lemma lem1117483 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term104 _26221 h t n) = (term104 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117482 _26221 h h' t n)). Qed.
Lemma lem1117484 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117485 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term105 _26221 h t n) = (term105 _26221 h t n).
Proof. exact (MK_COMB (@lem1117484 _26221) (@lem1117483 _26221 h t n)). Qed.
Lemma lem1117488 {_26221 : Type'} (t : list _26221) (n : nat) : (term94 _26221 t n) = (term94 _26221 t n).
Proof. exact (eq_refl (term94 _26221 t n)). Qed.
Lemma lem1117489 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (((@List.length _26221 t) = n) = (term105 _26221 h t n)) = (((@List.length _26221 t) = n) = (term105 _26221 h t n)).
Proof. exact (MK_COMB (@lem1117488 _26221 t n) (@lem1117485 _26221 h t n)). Qed.
Lemma lem1117490 {_26221 : Type'} (h : _26221) (t : list _26221) : (term106 _26221 h t) = (term106 _26221 h t).
Proof. exact (fun_ext (fun n : nat => @lem1117489 _26221 h t n)). Qed.
Lemma lem1117491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1117492 {_26221 : Type'} (h : _26221) (t : list _26221) : (term107 _26221 h t) = (term107 _26221 h t).
Proof. exact (MK_COMB (@lem1117491) (@lem1117490 _26221 h t)). Qed.
Lemma lem1117493 {_26221 : Type'} (t : list _26221) : (term117 _26221 t) = (term117 _26221 t).
Proof. exact (fun_ext (fun h : _26221 => @lem1117492 _26221 h t)). Qed.
Lemma lem1117494 {_26221 : Type'} : (@all _26221) = (@all _26221).
Proof. exact (eq_refl (@all _26221)). Qed.
Lemma lem1117495 {_26221 : Type'} (t : list _26221) : (term119 _26221 t) = (term119 _26221 t).
Proof. exact (MK_COMB (@lem1117494 _26221) (@lem1117493 _26221 t)). Qed.
Lemma lem1117496 {_26221 : Type'} : (term121 _26221) = (term121 _26221).
Proof. exact (fun_ext (fun t : list _26221 => @lem1117495 _26221 t)). Qed.
Lemma lem1117497 {_26221 : Type'} : (@all (list _26221)) = (@all (list _26221)).
Proof. exact (eq_refl (@all (list _26221))). Qed.
Lemma lem1117498 {_26221 : Type'} : (term123 _26221) = (term123 _26221).
Proof. exact (MK_COMB (@lem1117497 _26221) (@lem1117496 _26221)). Qed.
Lemma lem1117535 {_26221 : Type'} : (term122 _26221) = (term123 _26221).
Proof. exact (TRANS (@lem1117470 _26221) (@lem1117498 _26221)). Qed.
Lemma lem1117536 {_26221 : Type'} : (term123 _26221) = (term122 _26221).
Proof. exact (SYM (@lem1117535 _26221)). Qed.
Lemma lem1117538 (p : Prop) : p = (term108 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1117539 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (((@List.length _26221 t) = n) = (term105 _26221 h t n)) = (term124 _26221 h t n).
Proof. exact (@lem1117538 (((@List.length _26221 t) = n) = (term105 _26221 h t n))). Qed.
Lemma lem1117540 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term124 _26221 h t n) = (((@List.length _26221 t) = n) = (term105 _26221 h t n)).
Proof. exact (SYM (@lem1117539 _26221 h t n)). Qed.
Lemma lem1117541 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term125 _26221 h t n) : term125 _26221 h t n.
Proof. exact (h1). Qed.
Lemma lem1117552 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) : (term126 _26221 h h' t t') = (term127 _26221 h h' t t').
Proof. exact (@lem17045 (h = h') (t = t')). Qed.
Lemma lem1117556 {_26221 : Type'} (t' : list _26221) (n : nat) : (term128 _26221 t' n) = (term128 _26221 t' n).
Proof. exact (eq_refl (term128 _26221 t' n)). Qed.
Lemma lem1117558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1117559 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) : (term129 _26221 h h' t t') = (term130 _26221 h h' t t').
Proof. exact (MK_COMB (@lem1117558) (@lem1117552 _26221 h h' t t')). Qed.
Lemma lem1117560 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term131 _26221 h h' t t' n) = (term132 _26221 h h' t t' n).
Proof. exact (MK_COMB (@lem1117559 _26221 h h' t t') (@lem1117556 _26221 t' n)). Qed.
Lemma lem1117561 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term133 _26221 h h' t t' n) = (term131 _26221 h h' t t' n).
Proof. exact (@lem17045 (term90 _26221 h h' t t') ((@List.length _26221 t') = n)). Qed.
Lemma lem1117562 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term133 _26221 h h' t t' n) = (term132 _26221 h h' t t' n).
Proof. exact (TRANS (@lem1117561 _26221 h h' t t' n) (@lem1117560 _26221 h h' t t' n)). Qed.
Lemma lem1117565 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term98 _26221 h h' t t' n) = (term98 _26221 h h' t t' n).
Proof. exact (eq_refl (term98 _26221 h h' t t' n)). Qed.
Lemma lem1117566 {_26221 : Type'} (P : type1143 _26221) : (term134 _26221 P) = (term135 _26221 P).
Proof. exact (@lem18394 (list _26221) P). Qed.
Lemma lem1117567 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term136 _26221 h h' t n) = (term137 _26221 h h' t n).
Proof. exact (@lem1117566 _26221 (term100 _26221 h h' t n)). Qed.
Lemma lem1117568 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term138 _26221 h h' t n t') = (term98 _26221 h h' t t' n).
Proof. exact (eq_refl (term138 _26221 h h' t n t')). Qed.
Lemma lem1117569 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1117570 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term139 _26221 h h' t n t') = (term133 _26221 h h' t t' n).
Proof. exact (MK_COMB (@lem1117569) (@lem1117568 _26221 h h' t t' n)). Qed.
Lemma lem1117571 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term139 _26221 h h' t n t') = (term132 _26221 h h' t t' n).
Proof. exact (TRANS (@lem1117570 _26221 h h' t t' n) (@lem1117562 _26221 h h' t t' n)). Qed.
Lemma lem1117572 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term140 _26221 h h' t n) = (term141 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117571 _26221 h h' t t' n)). Qed.
Lemma lem1117573 {_26221 : Type'} : (@all (list _26221)) = (@all (list _26221)).
Proof. exact (eq_refl (@all (list _26221))). Qed.
Lemma lem1117574 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term137 _26221 h h' t n) = (term142 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117573 _26221) (@lem1117572 _26221 h h' t n)). Qed.
Lemma lem1117575 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term136 _26221 h h' t n) = (term142 _26221 h h' t n).
Proof. exact (TRANS (@lem1117567 _26221 h h' t n) (@lem1117574 _26221 h h' t n)). Qed.
Lemma lem1117576 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term100 _26221 h h' t n) = (term100 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117565 _26221 h h' t t' n)). Qed.
Lemma lem1117577 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117578 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term102 _26221 h h' t n) = (term102 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117577 _26221) (@lem1117576 _26221 h h' t n)). Qed.
Lemma lem1117579 {_26221 : Type'} (P : _26221 -> Prop) : (term143 _26221 P) = (term144 _26221 P).
Proof. exact (@lem18394 _26221 P). Qed.
Lemma lem1117580 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term145 _26221 h t n) = (term146 _26221 h t n).
Proof. exact (@lem1117579 _26221 (term104 _26221 h t n)). Qed.
Lemma lem1117581 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term147 _26221 h t n h') = (term102 _26221 h h' t n).
Proof. exact (eq_refl (term147 _26221 h t n h')). Qed.
Lemma lem1117582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1117583 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term148 _26221 h t n h') = (term136 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117582) (@lem1117581 _26221 h h' t n)). Qed.
Lemma lem1117584 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term148 _26221 h t n h') = (term142 _26221 h h' t n).
Proof. exact (TRANS (@lem1117583 _26221 h h' t n) (@lem1117575 _26221 h h' t n)). Qed.
Lemma lem1117585 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term149 _26221 h t n) = (term150 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117584 _26221 h h' t n)). Qed.
Lemma lem1117586 {_26221 : Type'} : (@all _26221) = (@all _26221).
Proof. exact (eq_refl (@all _26221)). Qed.
Lemma lem1117587 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term146 _26221 h t n) = (term151 _26221 h t n).
Proof. exact (MK_COMB (@lem1117586 _26221) (@lem1117585 _26221 h t n)). Qed.
Lemma lem1117588 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term145 _26221 h t n) = (term151 _26221 h t n).
Proof. exact (TRANS (@lem1117580 _26221 h t n) (@lem1117587 _26221 h t n)). Qed.
Lemma lem1117589 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term104 _26221 h t n) = (term104 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117578 _26221 h h' t n)). Qed.
Lemma lem1117590 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117591 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term105 _26221 h t n) = (term105 _26221 h t n).
Proof. exact (MK_COMB (@lem1117590 _26221) (@lem1117589 _26221 h t n)). Qed.
Lemma lem1117593 {_26221 : Type'} (t : list _26221) (n : nat) : (term152 _26221 t n) = (term152 _26221 t n).
Proof. exact (eq_refl (term152 _26221 t n)). Qed.
Lemma lem1117594 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term153 _26221 h t n) = (term153 _26221 h t n).
Proof. exact (MK_COMB (@lem1117593 _26221 t n) (@lem1117591 _26221 h t n)). Qed.
Lemma lem1117596 {_26221 : Type'} (t : list _26221) (n : nat) : (term154 _26221 t n) = (term154 _26221 t n).
Proof. exact (eq_refl (term154 _26221 t n)). Qed.
Lemma lem1117597 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term155 _26221 h t n) = (term156 _26221 h t n).
Proof. exact (MK_COMB (@lem1117596 _26221 t n) (@lem1117588 _26221 h t n)). Qed.
Lemma lem1117598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1117599 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term157 _26221 h t n) = (term158 _26221 h t n).
Proof. exact (MK_COMB (@lem1117598) (@lem1117597 _26221 h t n)). Qed.
Lemma lem1117600 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term159 _26221 h t n) = (term160 _26221 h t n).
Proof. exact (MK_COMB (@lem1117599 _26221 h t n) (@lem1117594 _26221 h t n)). Qed.
Lemma lem1117601 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term125 _26221 h t n) = (term159 _26221 h t n).
Proof. exact (@lem17646 ((@List.length _26221 t) = n) (term105 _26221 h t n)). Qed.
Lemma lem1117602 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term125 _26221 h t n) = (term160 _26221 h t n).
Proof. exact (TRANS (@lem1117601 _26221 h t n) (@lem1117600 _26221 h t n)). Qed.
Lemma lem1117709 {A : Type'} (P : Prop) (Q : A -> Prop) : (term161 A P Q) = (term162 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1117710 {_26221 : Type'} (P : Prop) (Q : _26221 -> Prop) : (term161 _26221 P Q) = (term162 _26221 P Q).
Proof. exact (@lem1117709 _26221 P Q). Qed.
Lemma lem1117711 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term163 _26221 h t n) = (term164 _26221 h t n).
Proof. exact (@lem1117710 _26221 (term128 _26221 t n) (term104 _26221 h t n)). Qed.
Lemma lem1117712 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term147 _26221 h t n h') = (term102 _26221 h h' t n).
Proof. exact (eq_refl (term147 _26221 h t n h')). Qed.
Lemma lem1117713 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term165 _26221 h t n) = (term104 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117712 _26221 h h' t n)). Qed.
Lemma lem1117714 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117715 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term166 _26221 h t n) = (term105 _26221 h t n).
Proof. exact (MK_COMB (@lem1117714 _26221) (@lem1117713 _26221 h t n)). Qed.
Lemma lem1117716 {_26221 : Type'} (t : list _26221) (n : nat) : (term152 _26221 t n) = (term152 _26221 t n).
Proof. exact (eq_refl (term152 _26221 t n)). Qed.
Lemma lem1117717 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term163 _26221 h t n) = (term153 _26221 h t n).
Proof. exact (MK_COMB (@lem1117716 _26221 t n) (@lem1117715 _26221 h t n)). Qed.
Lemma lem1117718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117719 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term167 _26221 h t n) = (term168 _26221 h t n).
Proof. exact (MK_COMB (@lem1117718) (@lem1117717 _26221 h t n)). Qed.
Lemma lem1117720 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term147 _26221 h t n h') = (term102 _26221 h h' t n).
Proof. exact (eq_refl (term147 _26221 h t n h')). Qed.
Lemma lem1117721 {_26221 : Type'} (t : list _26221) (n : nat) : (term152 _26221 t n) = (term152 _26221 t n).
Proof. exact (eq_refl (term152 _26221 t n)). Qed.
Lemma lem1117722 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term169 _26221 h t n h') = (term170 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117721 _26221 t n) (@lem1117720 _26221 h h' t n)). Qed.
Lemma lem1117723 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term171 _26221 h t n) = (term172 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117722 _26221 h h' t n)). Qed.
Lemma lem1117724 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117725 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term164 _26221 h t n) = (term173 _26221 h t n).
Proof. exact (MK_COMB (@lem1117724 _26221) (@lem1117723 _26221 h t n)). Qed.
Lemma lem1117726 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : ((term163 _26221 h t n) = (term164 _26221 h t n)) = ((term153 _26221 h t n) = (term173 _26221 h t n)).
Proof. exact (MK_COMB (@lem1117719 _26221 h t n) (@lem1117725 _26221 h t n)). Qed.
Lemma lem1117727 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term153 _26221 h t n) = (term173 _26221 h t n).
Proof. exact (EQ_MP (@lem1117726 _26221 h t n) (@lem1117711 _26221 h t n)). Qed.
Lemma lem1117729 {A : Type'} (P : Prop) (Q : A -> Prop) : (term161 A P Q) = (term162 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1117730 {_26221 : Type'} (P : Prop) (Q : type1143 _26221) : (term174 _26221 P Q) = (term175 _26221 P Q).
Proof. exact (@lem1117729 (list _26221) P Q). Qed.
Lemma lem1117731 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term176 _26221 h h' t n) = (term177 _26221 h h' t n).
Proof. exact (@lem1117730 _26221 (term128 _26221 t n) (term100 _26221 h h' t n)). Qed.
Lemma lem1117732 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term138 _26221 h h' t n t') = (term98 _26221 h h' t t' n).
Proof. exact (eq_refl (term138 _26221 h h' t n t')). Qed.
Lemma lem1117733 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term178 _26221 h h' t n) = (term100 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117732 _26221 h h' t t' n)). Qed.
Lemma lem1117734 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117735 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term179 _26221 h h' t n) = (term102 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117734 _26221) (@lem1117733 _26221 h h' t n)). Qed.
Lemma lem1117736 {_26221 : Type'} (t : list _26221) (n : nat) : (term152 _26221 t n) = (term152 _26221 t n).
Proof. exact (eq_refl (term152 _26221 t n)). Qed.
Lemma lem1117737 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term176 _26221 h h' t n) = (term170 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117736 _26221 t n) (@lem1117735 _26221 h h' t n)). Qed.
Lemma lem1117738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117739 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term180 _26221 h h' t n) = (term181 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117738) (@lem1117737 _26221 h h' t n)). Qed.
Lemma lem1117740 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term138 _26221 h h' t n t') = (term98 _26221 h h' t t' n).
Proof. exact (eq_refl (term138 _26221 h h' t n t')). Qed.
Lemma lem1117741 {_26221 : Type'} (t : list _26221) (n : nat) : (term152 _26221 t n) = (term152 _26221 t n).
Proof. exact (eq_refl (term152 _26221 t n)). Qed.
Lemma lem1117742 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term182 _26221 h h' t n t') = (term183 _26221 h h' t t' n).
Proof. exact (MK_COMB (@lem1117741 _26221 t n) (@lem1117740 _26221 h h' t t' n)). Qed.
Lemma lem1117743 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term184 _26221 h h' t n) = (term185 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117742 _26221 h h' t t' n)). Qed.
Lemma lem1117744 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117745 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term177 _26221 h h' t n) = (term186 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117744 _26221) (@lem1117743 _26221 h h' t n)). Qed.
Lemma lem1117746 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : ((term176 _26221 h h' t n) = (term177 _26221 h h' t n)) = ((term170 _26221 h h' t n) = (term186 _26221 h h' t n)).
Proof. exact (MK_COMB (@lem1117739 _26221 h h' t n) (@lem1117745 _26221 h h' t n)). Qed.
Lemma lem1117747 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term170 _26221 h h' t n) = (term186 _26221 h h' t n).
Proof. exact (EQ_MP (@lem1117746 _26221 h h' t n) (@lem1117731 _26221 h h' t n)). Qed.
Lemma lem1117748 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term172 _26221 h t n) = (term187 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117747 _26221 h h' t n)). Qed.
Lemma lem1117749 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117750 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term173 _26221 h t n) = (term188 _26221 h t n).
Proof. exact (MK_COMB (@lem1117749 _26221) (@lem1117748 _26221 h t n)). Qed.
Lemma lem1117751 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term153 _26221 h t n) = (term188 _26221 h t n).
Proof. exact (TRANS (@lem1117727 _26221 h t n) (@lem1117750 _26221 h t n)). Qed.
Lemma lem1117752 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term158 _26221 h t n) = (term158 _26221 h t n).
Proof. exact (eq_refl (term158 _26221 h t n)). Qed.
Lemma lem1117753 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term160 _26221 h t n) = (term189 _26221 h t n).
Proof. exact (MK_COMB (@lem1117752 _26221 h t n) (@lem1117751 _26221 h t n)). Qed.
Lemma lem1117755 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1117756 {_26221 : Type'} (P : Prop) (Q : _26221 -> Prop) : (term190 _26221 P Q) = (term191 _26221 P Q).
Proof. exact (@lem1117755 _26221 P Q). Qed.
Lemma lem1117757 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term192 _26221 h t n) = (term193 _26221 h t n).
Proof. exact (@lem1117756 _26221 (term156 _26221 h t n) (term187 _26221 h t n)). Qed.
Lemma lem1117758 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term194 _26221 h t n h') = (term186 _26221 h h' t n).
Proof. exact (eq_refl (term194 _26221 h t n h')). Qed.
Lemma lem1117759 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term195 _26221 h t n) = (term187 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117758 _26221 h h' t n)). Qed.
Lemma lem1117760 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117761 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term196 _26221 h t n) = (term188 _26221 h t n).
Proof. exact (MK_COMB (@lem1117760 _26221) (@lem1117759 _26221 h t n)). Qed.
Lemma lem1117762 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term158 _26221 h t n) = (term158 _26221 h t n).
Proof. exact (eq_refl (term158 _26221 h t n)). Qed.
Lemma lem1117763 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term192 _26221 h t n) = (term189 _26221 h t n).
Proof. exact (MK_COMB (@lem1117762 _26221 h t n) (@lem1117761 _26221 h t n)). Qed.
Lemma lem1117764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117765 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term197 _26221 h t n) = (term198 _26221 h t n).
Proof. exact (MK_COMB (@lem1117764) (@lem1117763 _26221 h t n)). Qed.
Lemma lem1117766 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term194 _26221 h t n h') = (term186 _26221 h h' t n).
Proof. exact (eq_refl (term194 _26221 h t n h')). Qed.
Lemma lem1117767 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term158 _26221 h t n) = (term158 _26221 h t n).
Proof. exact (eq_refl (term158 _26221 h t n)). Qed.
Lemma lem1117768 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term199 _26221 h t n h') = (term200 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117767 _26221 h t n) (@lem1117766 _26221 h h' t n)). Qed.
Lemma lem1117769 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term201 _26221 h t n) = (term202 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117768 _26221 h h' t n)). Qed.
Lemma lem1117770 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117771 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term193 _26221 h t n) = (term203 _26221 h t n).
Proof. exact (MK_COMB (@lem1117770 _26221) (@lem1117769 _26221 h t n)). Qed.
Lemma lem1117772 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : ((term192 _26221 h t n) = (term193 _26221 h t n)) = ((term189 _26221 h t n) = (term203 _26221 h t n)).
Proof. exact (MK_COMB (@lem1117765 _26221 h t n) (@lem1117771 _26221 h t n)). Qed.
Lemma lem1117773 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term189 _26221 h t n) = (term203 _26221 h t n).
Proof. exact (EQ_MP (@lem1117772 _26221 h t n) (@lem1117757 _26221 h t n)). Qed.
Lemma lem1117775 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1117776 {_26221 : Type'} (P : Prop) (Q : type1143 _26221) : (term204 _26221 P Q) = (term205 _26221 P Q).
Proof. exact (@lem1117775 (list _26221) P Q). Qed.
Lemma lem1117777 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term206 _26221 h h' t n) = (term207 _26221 h h' t n).
Proof. exact (@lem1117776 _26221 (term156 _26221 h t n) (term185 _26221 h h' t n)). Qed.
Lemma lem1117778 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term208 _26221 h h' t n t') = (term183 _26221 h h' t t' n).
Proof. exact (eq_refl (term208 _26221 h h' t n t')). Qed.
Lemma lem1117779 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term209 _26221 h h' t n) = (term185 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117778 _26221 h h' t t' n)). Qed.
Lemma lem1117780 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117781 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term210 _26221 h h' t n) = (term186 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117780 _26221) (@lem1117779 _26221 h h' t n)). Qed.
Lemma lem1117782 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term158 _26221 h t n) = (term158 _26221 h t n).
Proof. exact (eq_refl (term158 _26221 h t n)). Qed.
Lemma lem1117783 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term206 _26221 h h' t n) = (term200 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117782 _26221 h t n) (@lem1117781 _26221 h h' t n)). Qed.
Lemma lem1117784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117785 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term211 _26221 h h' t n) = (term212 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117784) (@lem1117783 _26221 h h' t n)). Qed.
Lemma lem1117786 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term208 _26221 h h' t n t') = (term183 _26221 h h' t t' n).
Proof. exact (eq_refl (term208 _26221 h h' t n t')). Qed.
Lemma lem1117787 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term158 _26221 h t n) = (term158 _26221 h t n).
Proof. exact (eq_refl (term158 _26221 h t n)). Qed.
Lemma lem1117788 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term213 _26221 h h' t n t') = (term214 _26221 h h' t t' n).
Proof. exact (MK_COMB (@lem1117787 _26221 h t n) (@lem1117786 _26221 h h' t t' n)). Qed.
Lemma lem1117789 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term215 _26221 h h' t n) = (term216 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117788 _26221 h h' t t' n)). Qed.
Lemma lem1117790 {_26221 : Type'} : (@ex (list _26221)) = (@ex (list _26221)).
Proof. exact (eq_refl (@ex (list _26221))). Qed.
Lemma lem1117791 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term207 _26221 h h' t n) = (term217 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117790 _26221) (@lem1117789 _26221 h h' t n)). Qed.
Lemma lem1117792 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : ((term206 _26221 h h' t n) = (term207 _26221 h h' t n)) = ((term200 _26221 h h' t n) = (term217 _26221 h h' t n)).
Proof. exact (MK_COMB (@lem1117785 _26221 h h' t n) (@lem1117791 _26221 h h' t n)). Qed.
Lemma lem1117793 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term200 _26221 h h' t n) = (term217 _26221 h h' t n).
Proof. exact (EQ_MP (@lem1117792 _26221 h h' t n) (@lem1117777 _26221 h h' t n)). Qed.
Lemma lem1117794 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term202 _26221 h t n) = (term218 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117793 _26221 h h' t n)). Qed.
Lemma lem1117795 {_26221 : Type'} : (@ex _26221) = (@ex _26221).
Proof. exact (eq_refl (@ex _26221)). Qed.
Lemma lem1117796 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term203 _26221 h t n) = (term219 _26221 h t n).
Proof. exact (MK_COMB (@lem1117795 _26221) (@lem1117794 _26221 h t n)). Qed.
Lemma lem1117797 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term189 _26221 h t n) = (term219 _26221 h t n).
Proof. exact (TRANS (@lem1117773 _26221 h t n) (@lem1117796 _26221 h t n)). Qed.
Lemma lem1117799 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term160 _26221 h t n) = (term219 _26221 h t n).
Proof. exact (TRANS (@lem1117753 _26221 h t n) (@lem1117797 _26221 h t n)). Qed.
Lemma lem1117800 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term125 _26221 h t n) = (term219 _26221 h t n).
Proof. exact (TRANS (@lem1117602 _26221 h t n) (@lem1117799 _26221 h t n)). Qed.
Lemma lem1117801 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term125 _26221 h t n) : term219 _26221 h t n.
Proof. exact (EQ_MP (@lem1117800 _26221 h t n) (@lem1117541 _26221 h t n h1)). Qed.
Lemma lem1117802 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) (h1 : term217 _26221 h h' t n) : term217 _26221 h h' t n.
Proof. exact (h1). Qed.
Lemma lem1117803 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term214 _26221 h h' t t' n) : term214 _26221 h h' t t' n.
Proof. exact (h1). Qed.
Lemma lem1117838 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term183 _26221 h h' t t' n) = (term183 _26221 h h' t t' n).
Proof. exact (eq_refl (term183 _26221 h h' t t' n)). Qed.
Lemma lem1117867 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term132 _26221 h h' t t' n) = (term132 _26221 h h' t t' n).
Proof. exact (eq_refl (term132 _26221 h h' t t' n)). Qed.
Lemma lem1117868 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term141 _26221 h h' t n) = (term141 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117867 _26221 h h' t t' n)). Qed.
Lemma lem1117869 {_26221 : Type'} : (@all (list _26221)) = (@all (list _26221)).
Proof. exact (eq_refl (@all (list _26221))). Qed.
Lemma lem1117870 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term142 _26221 h h' t n) = (term142 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117869 _26221) (@lem1117868 _26221 h h' t n)). Qed.
Lemma lem1117871 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term150 _26221 h t n) = (term150 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117870 _26221 h h' t n)). Qed.
Lemma lem1117872 {_26221 : Type'} : (@all _26221) = (@all _26221).
Proof. exact (eq_refl (@all _26221)). Qed.
Lemma lem1117873 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term151 _26221 h t n) = (term151 _26221 h t n).
Proof. exact (MK_COMB (@lem1117872 _26221) (@lem1117871 _26221 h t n)). Qed.
Lemma lem1117882 {_26221 : Type'} (t : list _26221) (n : nat) : (term154 _26221 t n) = (term154 _26221 t n).
Proof. exact (eq_refl (term154 _26221 t n)). Qed.
Lemma lem1117883 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term156 _26221 h t n) = (term156 _26221 h t n).
Proof. exact (MK_COMB (@lem1117882 _26221 t n) (@lem1117873 _26221 h t n)). Qed.
Lemma lem1117884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1117885 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term158 _26221 h t n) = (term158 _26221 h t n).
Proof. exact (MK_COMB (@lem1117884) (@lem1117883 _26221 h t n)). Qed.
Lemma lem1117886 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term214 _26221 h h' t t' n) = (term214 _26221 h h' t t' n).
Proof. exact (MK_COMB (@lem1117885 _26221 h t n) (@lem1117838 _26221 h h' t t' n)). Qed.
Lemma lem1117887 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term214 _26221 h h' t t' n) : term214 _26221 h h' t t' n.
Proof. exact (EQ_MP (@lem1117886 _26221 h h' t t' n) (@lem1117803 _26221 h h' t t' n h1)). Qed.
Lemma lem1117888 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term156 _26221 h t n.
Proof. exact (h1). Qed.
Lemma lem1117889 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term183 _26221 h h' t t' n.
Proof. exact (h1). Qed.
Lemma lem1117890 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term151 _26221 h t n.
Proof. exact (proj2 (@lem1117888 _26221 h t n h1)). Qed.
Lemma lem1117892 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term98 _26221 h h' t t' n.
Proof. exact (proj2 (@lem1117889 _26221 h h' t t' n h1)). Qed.
Lemma lem1117895 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term90 _26221 h h' t t'.
Proof. exact (proj1 (@lem1117892 _26221 h h' t t' n h1)). Qed.
Lemma lem1117915 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) : (term132 _26221 h h' t t' n) = (term132 _26221 h h' t t' n).
Proof. exact (eq_refl (term132 _26221 h h' t t' n)). Qed.
Lemma lem1117916 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term141 _26221 h h' t n) = (term141 _26221 h h' t n).
Proof. exact (fun_ext (fun t' : list _26221 => @lem1117915 _26221 h h' t t' n)). Qed.
Lemma lem1117917 {_26221 : Type'} : (@all (list _26221)) = (@all (list _26221)).
Proof. exact (eq_refl (@all (list _26221))). Qed.
Lemma lem1117918 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) : (term142 _26221 h h' t n) = (term142 _26221 h h' t n).
Proof. exact (MK_COMB (@lem1117917 _26221) (@lem1117916 _26221 h h' t n)). Qed.
Lemma lem1117919 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term150 _26221 h t n) = (term150 _26221 h t n).
Proof. exact (fun_ext (fun h' : _26221 => @lem1117918 _26221 h h' t n)). Qed.
Lemma lem1117920 {_26221 : Type'} : (@all _26221) = (@all _26221).
Proof. exact (eq_refl (@all _26221)). Qed.
Lemma lem1117922 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : (term151 _26221 h t n) = (term151 _26221 h t n).
Proof. exact (MK_COMB (@lem1117920 _26221) (@lem1117919 _26221 h t n)). Qed.
Lemma lem1117923 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term151 _26221 h t n.
Proof. exact (EQ_MP (@lem1117922 _26221 h t n) (@lem1117890 _26221 h t n h1)). Qed.
Lemma lem1117940 {_26221 : Type'} (_18143 : _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term220 _26221 h t n _18143.
Proof. exact (@lem1117923 _26221 h t n h1 _18143). Qed.
Lemma lem1117941 {_26221 : Type'} (h : _26221) (_18143 : _26221) (t : list _26221) (n : nat) : (term220 _26221 h t n _18143) = (term142 _26221 h _18143 t n).
Proof. exact (eq_refl (term220 _26221 h t n _18143)). Qed.
Lemma lem1117942 {_26221 : Type'} (_18143 : _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term142 _26221 h _18143 t n.
Proof. exact (EQ_MP (@lem1117941 _26221 h _18143 t n) (@lem1117940 _26221 _18143 h t n h1)). Qed.
Lemma lem1117943 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term221 _26221 h _18143 t n _18144.
Proof. exact (@lem1117942 _26221 _18143 h t n h1 _18144). Qed.
Lemma lem1117944 {_26221 : Type'} (h : _26221) (_18143 : _26221) (t : list _26221) (_18144 : list _26221) (n : nat) : (term221 _26221 h _18143 t n _18144) = (term132 _26221 h _18143 t _18144 n).
Proof. exact (eq_refl (term221 _26221 h _18143 t n _18144)). Qed.
Lemma lem1117945 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term132 _26221 h _18143 t _18144 n.
Proof. exact (EQ_MP (@lem1117944 _26221 h _18143 t _18144 n) (@lem1117943 _26221 _18143 _18144 h t n h1)). Qed.
Lemma lem1117947 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : (@List.length _26221 t) = n.
Proof. exact (proj1 (@lem1117888 _26221 h t n h1)). Qed.
Lemma lem1117958 {_26221 : Type'} (h : _26221) (_18143 : _26221) (t : list _26221) (_18144 : list _26221) (n : nat) : (term132 _26221 h _18143 t _18144 n) = (term222 _26221 h _18143 t _18144 n).
Proof. exact (@lem1117076 (term223 _26221 h _18143) (term224 _26221 t _18144) (term128 _26221 _18144 n)). Qed.
Lemma lem1117959 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term222 _26221 h _18143 t _18144 n.
Proof. exact (EQ_MP (@lem1117958 _26221 h _18143 t _18144 n) (@lem1117945 _26221 _18143 _18144 h t n h1)). Qed.
Lemma lem1117961 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term128 _26221 t n.
Proof. exact (proj1 (@lem1117889 _26221 h h' t t' n h1)). Qed.
Lemma lem1117967 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : t = t'.
Proof. exact (proj2 (@lem1117895 _26221 h h' t t' n h1)). Qed.
Lemma lem1117968 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : n = (@List.length _26221 t).
Proof. exact (SYM (@lem1117947 _26221 h t n h1)). Qed.
Lemma lem1117983 {_26221 : Type'} (h : _26221) (_18143 : _26221) (t : list _26221) (_18144 : list _26221) : (term225 _26221 h _18143 t _18144) = (term225 _26221 h _18143 t _18144).
Proof. exact (eq_refl (term225 _26221 h _18143 t _18144)). Qed.
Lemma lem1117984 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : (term226 _26221 h _18143 t _18144 n) = (term227 _26221 h _18143 _18144 t).
Proof. exact (MK_COMB (@lem1117983 _26221 h _18143 t _18144) (@lem1117968 _26221 h t n h1)). Qed.
Lemma lem1117985 {_26221 : Type'} (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : (term227 _26221 h _18143 _18144 t) = (term228 _26221 h _18143 _18144 t).
Proof. exact (eq_refl (term227 _26221 h _18143 _18144 t)). Qed.
Lemma lem1117986 {_26221 : Type'} (h : _26221) (_18143 : _26221) (t : list _26221) (_18144 : list _26221) (n : nat) : (term229 _26221 h _18143 t _18144 n) = (term229 _26221 h _18143 t _18144 n).
Proof. exact (eq_refl (term229 _26221 h _18143 t _18144 n)). Qed.
Lemma lem1117987 {_26221 : Type'} (n : nat) (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : ((term226 _26221 h _18143 t _18144 n) = (term227 _26221 h _18143 _18144 t)) = ((term226 _26221 h _18143 t _18144 n) = (term228 _26221 h _18143 _18144 t)).
Proof. exact (MK_COMB (@lem1117986 _26221 h _18143 t _18144 n) (@lem1117985 _26221 h _18143 _18144 t)). Qed.
Lemma lem1117988 {_26221 : Type'} (h : _26221) (_18143 : _26221) (t : list _26221) (_18144 : list _26221) (n : nat) : (term226 _26221 h _18143 t _18144 n) = (term222 _26221 h _18143 t _18144 n).
Proof. exact (eq_refl (term226 _26221 h _18143 t _18144 n)). Qed.
Lemma lem1117989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1117990 {_26221 : Type'} (h : _26221) (_18143 : _26221) (t : list _26221) (_18144 : list _26221) (n : nat) : (term229 _26221 h _18143 t _18144 n) = (term230 _26221 h _18143 t _18144 n).
Proof. exact (MK_COMB (@lem1117989) (@lem1117988 _26221 h _18143 t _18144 n)). Qed.
Lemma lem1117991 {_26221 : Type'} (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : (term228 _26221 h _18143 _18144 t) = (term228 _26221 h _18143 _18144 t).
Proof. exact (eq_refl (term228 _26221 h _18143 _18144 t)). Qed.
Lemma lem1117992 {_26221 : Type'} (n : nat) (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : ((term226 _26221 h _18143 t _18144 n) = (term228 _26221 h _18143 _18144 t)) = ((term222 _26221 h _18143 t _18144 n) = (term228 _26221 h _18143 _18144 t)).
Proof. exact (MK_COMB (@lem1117990 _26221 h _18143 t _18144 n) (@lem1117991 _26221 h _18143 _18144 t)). Qed.
Lemma lem1117993 {_26221 : Type'} (n : nat) (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : ((term226 _26221 h _18143 t _18144 n) = (term227 _26221 h _18143 _18144 t)) = ((term222 _26221 h _18143 t _18144 n) = (term228 _26221 h _18143 _18144 t)).
Proof. exact (TRANS (@lem1117987 _26221 n h _18143 _18144 t) (@lem1117992 _26221 n h _18143 _18144 t)). Qed.
Lemma lem1117994 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : (term222 _26221 h _18143 t _18144 n) = (term228 _26221 h _18143 _18144 t).
Proof. exact (EQ_MP (@lem1117993 _26221 n h _18143 _18144 t) (@lem1117984 _26221 _18143 _18144 h t n h1)). Qed.
Lemma lem1117995 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term228 _26221 h _18143 _18144 t.
Proof. exact (EQ_MP (@lem1117994 _26221 _18143 _18144 h t n h1) (@lem1117959 _26221 _18143 _18144 h t n h1)). Qed.
Lemma lem1118010 {_26221 : Type'} (n : nat) : (term231 _26221 n) = (term231 _26221 n).
Proof. exact (eq_refl (term231 _26221 n)). Qed.
Lemma lem1118011 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : (term232 _26221 n t) = (term232 _26221 n t').
Proof. exact (MK_COMB (@lem1118010 _26221 n) (@lem1117967 _26221 h h' t t' n h1)). Qed.
Lemma lem1118012 {_26221 : Type'} (t' : list _26221) (n : nat) : (term232 _26221 n t') = (term128 _26221 t' n).
Proof. exact (eq_refl (term232 _26221 n t')). Qed.
Lemma lem1118013 {_26221 : Type'} (n : nat) (t : list _26221) : (term233 _26221 n t) = (term233 _26221 n t).
Proof. exact (eq_refl (term233 _26221 n t)). Qed.
Lemma lem1118014 {_26221 : Type'} (t : list _26221) (t' : list _26221) (n : nat) : ((term232 _26221 n t) = (term232 _26221 n t')) = ((term232 _26221 n t) = (term128 _26221 t' n)).
Proof. exact (MK_COMB (@lem1118013 _26221 n t) (@lem1118012 _26221 t' n)). Qed.
Lemma lem1118015 {_26221 : Type'} (t : list _26221) (n : nat) : (term232 _26221 n t) = (term128 _26221 t n).
Proof. exact (eq_refl (term232 _26221 n t)). Qed.
Lemma lem1118016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1118017 {_26221 : Type'} (t : list _26221) (n : nat) : (term233 _26221 n t) = (term234 _26221 t n).
Proof. exact (MK_COMB (@lem1118016) (@lem1118015 _26221 t n)). Qed.
Lemma lem1118018 {_26221 : Type'} (t' : list _26221) (n : nat) : (term128 _26221 t' n) = (term128 _26221 t' n).
Proof. exact (eq_refl (term128 _26221 t' n)). Qed.
Lemma lem1118019 {_26221 : Type'} (t : list _26221) (t' : list _26221) (n : nat) : ((term232 _26221 n t) = (term128 _26221 t' n)) = ((term128 _26221 t n) = (term128 _26221 t' n)).
Proof. exact (MK_COMB (@lem1118017 _26221 t n) (@lem1118018 _26221 t' n)). Qed.
Lemma lem1118020 {_26221 : Type'} (t : list _26221) (t' : list _26221) (n : nat) : ((term232 _26221 n t) = (term232 _26221 n t')) = ((term128 _26221 t n) = (term128 _26221 t' n)).
Proof. exact (TRANS (@lem1118014 _26221 t t' n) (@lem1118019 _26221 t t' n)). Qed.
Lemma lem1118021 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : (term128 _26221 t n) = (term128 _26221 t' n).
Proof. exact (EQ_MP (@lem1118020 _26221 t t' n) (@lem1118011 _26221 h h' t t' n h1)). Qed.
Lemma lem1118078 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term128 _26221 t' n.
Proof. exact (EQ_MP (@lem1118021 _26221 h h' t t' n h1) (@lem1117961 _26221 h h' t t' n h1)). Qed.
Lemma lem1118092 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : (@List.length _26221 t') = n.
Proof. exact (proj2 (@lem1117892 _26221 h h' t t' n h1)). Qed.
Lemma lem1118093 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : n = (@List.length _26221 t').
Proof. exact (SYM (@lem1118092 _26221 h h' t t' n h1)). Qed.
Lemma lem1118108 {_26221 : Type'} (t' : list _26221) : (term235 _26221 t') = (term235 _26221 t').
Proof. exact (eq_refl (term235 _26221 t')). Qed.
Lemma lem1118109 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : (term236 _26221 t' n) = (term237 _26221 t').
Proof. exact (MK_COMB (@lem1118108 _26221 t') (@lem1118093 _26221 h h' t t' n h1)). Qed.
Lemma lem1118110 {_26221 : Type'} (t' : list _26221) : (term237 _26221 t') = (term238 _26221 t').
Proof. exact (eq_refl (term237 _26221 t')). Qed.
Lemma lem1118111 {_26221 : Type'} (t' : list _26221) (n : nat) : (term239 _26221 t' n) = (term239 _26221 t' n).
Proof. exact (eq_refl (term239 _26221 t' n)). Qed.
Lemma lem1118112 {_26221 : Type'} (n : nat) (t' : list _26221) : ((term236 _26221 t' n) = (term237 _26221 t')) = ((term236 _26221 t' n) = (term238 _26221 t')).
Proof. exact (MK_COMB (@lem1118111 _26221 t' n) (@lem1118110 _26221 t')). Qed.
Lemma lem1118113 {_26221 : Type'} (t' : list _26221) (n : nat) : (term236 _26221 t' n) = (term128 _26221 t' n).
Proof. exact (eq_refl (term236 _26221 t' n)). Qed.
Lemma lem1118114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1118115 {_26221 : Type'} (t' : list _26221) (n : nat) : (term239 _26221 t' n) = (term234 _26221 t' n).
Proof. exact (MK_COMB (@lem1118114) (@lem1118113 _26221 t' n)). Qed.
Lemma lem1118116 {_26221 : Type'} (t' : list _26221) : (term238 _26221 t') = (term238 _26221 t').
Proof. exact (eq_refl (term238 _26221 t')). Qed.
Lemma lem1118117 {_26221 : Type'} (n : nat) (t' : list _26221) : ((term236 _26221 t' n) = (term238 _26221 t')) = ((term128 _26221 t' n) = (term238 _26221 t')).
Proof. exact (MK_COMB (@lem1118115 _26221 t' n) (@lem1118116 _26221 t')). Qed.
Lemma lem1118118 {_26221 : Type'} (n : nat) (t' : list _26221) : ((term236 _26221 t' n) = (term237 _26221 t')) = ((term128 _26221 t' n) = (term238 _26221 t')).
Proof. exact (TRANS (@lem1118112 _26221 n t') (@lem1118117 _26221 n t')). Qed.
Lemma lem1118119 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : (term128 _26221 t' n) = (term238 _26221 t').
Proof. exact (EQ_MP (@lem1118118 _26221 n t') (@lem1118109 _26221 h h' t t' n h1)). Qed.
Lemma lem1118120 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term238 _26221 t'.
Proof. exact (EQ_MP (@lem1118119 _26221 h h' t t' n h1) (@lem1118078 _26221 h h' t t' n h1)). Qed.
Lemma lem1118136 {_26221 : Type'} (x : _26221) : x = x.
Proof. exact (@lem21386 _26221 x). Qed.
Lemma lem1118137 {_26221 : Type'} (x : _26221) : x = x.
Proof. exact (@lem1118136 _26221 x). Qed.
Lemma lem1118138 {_26221 : Type'} (h : _26221) : h = h.
Proof. exact (@lem1118137 _26221 h). Qed.
Lemma lem1118139 {_26221 : Type'} (h : _26221) : term240 _26221 h.
Proof. exact (fun h0 : term241 _26221 h => @lem1118138 _26221 h). Qed.
Lemma lem1118141 (p : Prop) : (term242 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1118142 {_26221 : Type'} (h : _26221) : (term240 _26221 h) = (h = h).
Proof. exact (@lem1118141 (h = h)). Qed.
Lemma lem1118143 {_26221 : Type'} (h : _26221) : h = h.
Proof. exact (EQ_MP (@lem1118142 _26221 h) (@lem1118139 _26221 h)). Qed.
Lemma lem1118145 {_26221 : Type'} (x : list _26221) : x = x.
Proof. exact (@lem21386 (list _26221) x). Qed.
Lemma lem1118146 {_26221 : Type'} (x : list _26221) : x = x.
Proof. exact (@lem1118145 _26221 x). Qed.
Lemma lem1118147 {_26221 : Type'} (t : list _26221) : t = t.
Proof. exact (@lem1118146 _26221 t). Qed.
Lemma lem1118148 {_26221 : Type'} (t : list _26221) : term243 _26221 t.
Proof. exact (fun h0 : term244 _26221 t => @lem1118147 _26221 t). Qed.
Lemma lem1118150 (p : Prop) : (term242 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1118151 {_26221 : Type'} (t : list _26221) : (term243 _26221 t) = (t = t).
Proof. exact (@lem1118150 (t = t)). Qed.
Lemma lem1118152 {_26221 : Type'} (t : list _26221) : t = t.
Proof. exact (EQ_MP (@lem1118151 _26221 t) (@lem1118148 _26221 t)). Qed.
Lemma lem1118154 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1118155 {_26221 : Type'} (t : list _26221) : (@List.length _26221 t) = (@List.length _26221 t).
Proof. exact (@lem1118154 (@List.length _26221 t)). Qed.
Lemma lem1118156 {_26221 : Type'} (t : list _26221) : term245 _26221 t.
Proof. exact (fun h0 : term238 _26221 t => @lem1118155 _26221 t). Qed.
Lemma lem1118158 (p : Prop) : (term242 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1118159 {_26221 : Type'} (t : list _26221) : (term245 _26221 t) = ((@List.length _26221 t) = (@List.length _26221 t)).
Proof. exact (@lem1118158 ((@List.length _26221 t) = (@List.length _26221 t))). Qed.
Lemma lem1118160 {_26221 : Type'} (t : list _26221) : (@List.length _26221 t) = (@List.length _26221 t).
Proof. exact (EQ_MP (@lem1118159 _26221 t) (@lem1118156 _26221 t)). Qed.
Lemma lem1118162 (a : Prop) (b : Prop) : (term246 a b) = (term247 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1118163 {_26221 : Type'} (_18144 : list _26221) (t : list _26221) : (term248 _26221 _18144 t) = (term249 _26221 _18144 t).
Proof. exact (@lem1118162 (t = _18144) ((@List.length _26221 _18144) = (@List.length _26221 t))). Qed.
Lemma lem1118164 {_26221 : Type'} (h : _26221) (_18143 : _26221) : (term250 _26221 h _18143) = (term250 _26221 h _18143).
Proof. exact (eq_refl (term250 _26221 h _18143)). Qed.
Lemma lem1118165 {_26221 : Type'} (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : (term228 _26221 h _18143 _18144 t) = (term251 _26221 h _18143 _18144 t).
Proof. exact (MK_COMB (@lem1118164 _26221 h _18143) (@lem1118163 _26221 _18144 t)). Qed.
Lemma lem1118167 (a : Prop) (b : Prop) : (term246 a b) = (term247 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1118168 {_26221 : Type'} (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : (term251 _26221 h _18143 _18144 t) = (term252 _26221 h _18143 _18144 t).
Proof. exact (@lem1118167 (h = _18143) (term253 _26221 _18144 t)). Qed.
Lemma lem1118169 {_26221 : Type'} (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : (term228 _26221 h _18143 _18144 t) = (term252 _26221 h _18143 _18144 t).
Proof. exact (TRANS (@lem1118165 _26221 h _18143 _18144 t) (@lem1118168 _26221 h _18143 _18144 t)). Qed.
Lemma lem1118171 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1118172 {_26221 : Type'} (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : (term252 _26221 h _18143 _18144 t) = (term254 _26221 h _18143 _18144 t).
Proof. exact (@lem1118171 (term255 _26221 h _18143 _18144 t)). Qed.
Lemma lem1118173 {_26221 : Type'} (h : _26221) (_18143 : _26221) (_18144 : list _26221) (t : list _26221) : (term228 _26221 h _18143 _18144 t) = (term254 _26221 h _18143 _18144 t).
Proof. exact (TRANS (@lem1118169 _26221 h _18143 _18144 t) (@lem1118172 _26221 h _18143 _18144 t)). Qed.
Lemma lem1118175 {_26221 : Type'} (t : list _26221) : term256 _26221 t.
Proof. exact (conj (@lem1118152 _26221 t) (@lem1118160 _26221 t)). Qed.
Lemma lem1118176 {_26221 : Type'} (h : _26221) (t : list _26221) : term257 _26221 h t.
Proof. exact (conj (@lem1118143 _26221 h) (@lem1118175 _26221 t)). Qed.
Lemma lem1118178 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term254 _26221 h _18143 _18144 t.
Proof. exact (EQ_MP (@lem1118173 _26221 h _18143 _18144 t) (@lem1117995 _26221 _18143 _18144 h t n h1)). Qed.
Lemma lem1118179 {_26221 : Type'} (_18143 : _26221) (_18144 : list _26221) (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term254 _26221 h _18143 _18144 t.
Proof. exact (@lem1118178 _26221 _18143 _18144 h t n h1). Qed.
Lemma lem1118180 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term258 _26221 h t.
Proof. exact (@lem1118179 _26221 h t h t n h1). Qed.
Lemma lem1118183 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : False.
Proof. exact (@lem1118180 _26221 h t n h1 (@lem1118176 _26221 h t)). Qed.
Lemma lem1118184 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : term259.
Proof. exact (fun h0 : ~ False => @lem1118183 _26221 h t n h1). Qed.
Lemma lem1118186 (p : Prop) : (term242 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1118187 : term259 = False.
Proof. exact (@lem1118186 False). Qed.
Lemma lem1118202 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1118203 {_26221 : Type'} (t' : list _26221) : (@List.length _26221 t') = (@List.length _26221 t').
Proof. exact (@lem1118202 (@List.length _26221 t')). Qed.
Lemma lem1118204 {_26221 : Type'} (t' : list _26221) : term245 _26221 t'.
Proof. exact (fun h0 : term238 _26221 t' => @lem1118203 _26221 t'). Qed.
Lemma lem1118206 (p : Prop) : (term242 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1118207 {_26221 : Type'} (t' : list _26221) : (term245 _26221 t') = ((@List.length _26221 t') = (@List.length _26221 t')).
Proof. exact (@lem1118206 ((@List.length _26221 t') = (@List.length _26221 t'))). Qed.
Lemma lem1118208 {_26221 : Type'} (t' : list _26221) : (@List.length _26221 t') = (@List.length _26221 t').
Proof. exact (EQ_MP (@lem1118207 _26221 t') (@lem1118204 _26221 t')). Qed.
Lemma lem1118211 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1118213 {_26221 : Type'} (t' : list _26221) : (term238 _26221 t') = (term260 _26221 t').
Proof. exact (@lem1118211 ((@List.length _26221 t') = (@List.length _26221 t'))). Qed.
Lemma lem1118216 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term260 _26221 t'.
Proof. exact (EQ_MP (@lem1118213 _26221 t') (@lem1118120 _26221 h h' t t' n h1)). Qed.
Lemma lem1118219 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : False.
Proof. exact (@lem1118216 _26221 h h' t t' n h1 (@lem1118208 _26221 t')). Qed.
Lemma lem1118220 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : term259.
Proof. exact (fun h0 : ~ False => @lem1118219 _26221 h h' t t' n h1). Qed.
Lemma lem1118222 (p : Prop) : (term242 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1118223 : term259 = False.
Proof. exact (@lem1118222 False). Qed.
Lemma lem1118227 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term183 _26221 h h' t t' n) : False.
Proof. exact (EQ_MP (@lem1118223) (@lem1118220 _26221 h h' t t' n h1)). Qed.
Lemma lem1118228 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term156 _26221 h t n) : False.
Proof. exact (EQ_MP (@lem1118187) (@lem1118184 _26221 h t n h1)). Qed.
Lemma lem1118229 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term214 _26221 h h' t t' n) : False.
Proof. exact (or_elim (@lem1117887 _26221 h h' t t' n h1) (fun h0 : term156 _26221 h t n => @lem1118228 _26221 h t n h0) (fun h0 : term183 _26221 h h' t t' n => @lem1118227 _26221 h h' t t' n h0)). Qed.
Lemma lem1118230 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term214 _26221 h h' t t' n) : (term214 _26221 h h' t t' n) = False.
Proof. exact (prop_ext (fun h2 : term214 _26221 h h' t t' n => @lem1118229 _26221 h h' t t' n h1) (fun h2 : False => @lem1117887 _26221 h h' t t' n h1)). Qed.
Lemma lem1118231 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (t' : list _26221) (n : nat) (h1 : term214 _26221 h h' t t' n) : False.
Proof. exact (EQ_MP (@lem1118230 _26221 h h' t t' n h1) (@lem1117887 _26221 h h' t t' n h1)). Qed.
Lemma lem1118232 {_26221 : Type'} (h : _26221) (h' : _26221) (t : list _26221) (n : nat) (h1 : term217 _26221 h h' t n) : False.
Proof. exact (ex_elim (@lem1117802 _26221 h h' t n h1) (fun t' : list _26221 => fun h0 : term216 _26221 h h' t n t' => @lem1118231 _26221 h h' t t' n h0)). Qed.
Lemma lem1118233 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term125 _26221 h t n) : False.
Proof. exact (ex_elim (@lem1117801 _26221 h t n h1) (fun h' : _26221 => fun h0 : term218 _26221 h t n h' => @lem1118232 _26221 h h' t n h0)). Qed.
Lemma lem1118234 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term125 _26221 h t n) : (term125 _26221 h t n) = False.
Proof. exact (prop_ext (fun h2 : term125 _26221 h t n => @lem1118233 _26221 h t n h1) (fun h2 : False => @lem1117541 _26221 h t n h1)). Qed.
Lemma lem1118235 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) (h1 : term125 _26221 h t n) : False.
Proof. exact (EQ_MP (@lem1118234 _26221 h t n h1) (@lem1117541 _26221 h t n h1)). Qed.
Lemma lem1118236 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : term124 _26221 h t n.
Proof. exact (fun h0 : term125 _26221 h t n => @lem1118235 _26221 h t n h0). Qed.
Lemma lem1118237 {_26221 : Type'} (h : _26221) (t : list _26221) (n : nat) : ((@List.length _26221 t) = n) = (term105 _26221 h t n).
Proof. exact (EQ_MP (@lem1117540 _26221 h t n) (@lem1118236 _26221 h t n)). Qed.
Lemma lem1118242 {_26221 : Type'} (h : _26221) (t : list _26221) : term107 _26221 h t.
Proof. exact (fun n : nat => @lem1118237 _26221 h t n). Qed.
Lemma lem1118247 {_26221 : Type'} (t : list _26221) : term119 _26221 t.
Proof. exact (fun h : _26221 => @lem1118242 _26221 h t). Qed.
Lemma lem1118252 {_26221 : Type'} : term123 _26221.
Proof. exact (fun t : list _26221 => @lem1118247 _26221 t). Qed.
Lemma lem1118253 {_26221 : Type'} : term122 _26221.
Proof. exact (EQ_MP (@lem1117536 _26221) (@lem1118252 _26221)). Qed.
Lemma lem1118254 {_26221 : Type'} (t : list _26221) : term261 _26221 t.
Proof. exact (@lem1118253 _26221 t). Qed.
Lemma lem1118255 {_26221 : Type'} (t : list _26221) : (term261 _26221 t) = (term118 _26221 t).
Proof. exact (eq_refl (term261 _26221 t)). Qed.
Lemma lem1118256 {_26221 : Type'} (t : list _26221) : term118 _26221 t.
Proof. exact (EQ_MP (@lem1118255 _26221 t) (@lem1118254 _26221 t)). Qed.
Lemma lem1118257 {_26221 : Type'} (t : list _26221) (h : _26221) : term262 _26221 t h.
Proof. exact (@lem1118256 _26221 t h). Qed.
Lemma lem1118258 {_26221 : Type'} (h : _26221) (t : list _26221) : (term262 _26221 t h) = (term109 _26221 h t).
Proof. exact (eq_refl (term262 _26221 t h)). Qed.
Lemma lem1118259 {_26221 : Type'} (h : _26221) (t : list _26221) : term109 _26221 h t.
Proof. exact (EQ_MP (@lem1118258 _26221 h t) (@lem1118257 _26221 t h)). Qed.
Lemma lem1118261 {_26221 : Type'} (h : _26221) (t : list _26221) : term109 _26221 h t.
Proof. exact (@lem1117377 _26221 h t (@lem1118259 _26221 h t)). Qed.
Lemma lem1118262 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term110 _26221 h t) : False.
Proof. exact (@lem1118261 _26221 h t (@lem1117361 _26221 h t h1)). Qed.
Lemma lem1118263 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term110 _26221 h t) : (term110 _26221 h t) = False.
Proof. exact (prop_ext (fun h2 : term110 _26221 h t => @lem1118262 _26221 h t h1) (fun h2 : False => @lem1117361 _26221 h t h1)). Qed.
Lemma lem1118264 {_26221 : Type'} (h : _26221) (t : list _26221) (h1 : term110 _26221 h t) : False.
Proof. exact (EQ_MP (@lem1118263 _26221 h t h1) (@lem1117361 _26221 h t h1)). Qed.
Lemma lem1118265 {_26221 : Type'} (h : _26221) (t : list _26221) : term109 _26221 h t.
Proof. exact (fun h0 : term110 _26221 h t => @lem1118264 _26221 h t h0). Qed.
Lemma lem1118266 {_26221 : Type'} (h : _26221) (t : list _26221) : term107 _26221 h t.
Proof. exact (EQ_MP (@lem1117360 _26221 h t) (@lem1118265 _26221 h t)). Qed.
Lemma lem1118267 {_26221 : Type'} (h : _26221) (t : list _26221) : term82 _26221 h t.
Proof. exact (EQ_MP (@lem1117356 _26221 h t) (@lem1118266 _26221 h t)). Qed.
Lemma lem1118268 {_26221 : Type'} (h : _26221) (t : list _26221) : term35 _26221 h t.
Proof. exact (EQ_MP (@lem1117269 _26221 h t) (@lem1118267 _26221 h t)). Qed.
Lemma lem1118269 {_26221 : Type'} (h : _26221) (t : list _26221) : term37 _26221 h t.
Proof. exact (fun h0 : term31 _26221 t => @lem1118268 _26221 h t). Qed.
Lemma lem1118274 {_26221 : Type'} (h : _26221) : term41 _26221 h.
Proof. exact (fun t : list _26221 => @lem1118269 _26221 h t). Qed.
Lemma lem1118279 {_26221 : Type'} : term45 _26221.
Proof. exact (fun h : _26221 => @lem1118274 _26221 h). Qed.
Lemma lem1118280 {_26221 : Type'} : term47 _26221.
Proof. exact (conj (@lem1117224 _26221) (@lem1118279 _26221)). Qed.
Lemma lem1118281 {_26221 : Type'} : term52 _26221.
Proof. exact (@lem1117146 _26221 (@lem1118280 _26221)). Qed.
