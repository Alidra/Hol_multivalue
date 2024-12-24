Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_MONO_term_abbrevs.
Require Import SUBSET_CROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4339139 {_104190 _104196 : Type'} (s : _104190 -> Prop) : term0 _104190 _104196 s.
Proof. exact (@lem4339138 _104190 _104196 s). Qed.
Lemma lem4339140 {_104190 _104196 : Type'} (s : _104190 -> Prop) : (term0 _104190 _104196 s) = (term1 _104190 _104196 s).
Proof. exact (eq_refl (term0 _104190 _104196 s)). Qed.
Lemma lem4339141 {_104190 _104196 : Type'} (s : _104190 -> Prop) : term1 _104190 _104196 s.
Proof. exact (EQ_MP (@lem4339140 _104190 _104196 s) (@lem4339139 _104190 _104196 s)). Qed.
Lemma lem4339142 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : term2 _104190 _104196 s t.
Proof. exact (@lem4339141 _104190 _104196 s t). Qed.
Lemma lem4339143 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : (term2 _104190 _104196 s t) = (term3 _104190 _104196 s t).
Proof. exact (eq_refl (term2 _104190 _104196 s t)). Qed.
Lemma lem4339144 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : term3 _104190 _104196 s t.
Proof. exact (EQ_MP (@lem4339143 _104190 _104196 s t) (@lem4339142 _104190 _104196 s t)). Qed.
Lemma lem4339145 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) : term4 _104190 _104196 s t s'.
Proof. exact (@lem4339144 _104190 _104196 s t s'). Qed.
Lemma lem4339146 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : (term4 _104190 _104196 s t s') = (term5 _104190 _104196 s s' t).
Proof. exact (eq_refl (term4 _104190 _104196 s t s')). Qed.
Lemma lem4339147 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : term5 _104190 _104196 s s' t.
Proof. exact (EQ_MP (@lem4339146 _104190 _104196 s s' t) (@lem4339145 _104190 _104196 s t s')). Qed.
Lemma lem4339148 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : term6 _104190 _104196 s s' t t'.
Proof. exact (@lem4339147 _104190 _104196 s s' t t'). Qed.
Lemma lem4339149 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term6 _104190 _104196 s s' t t') = ((term7 _104190 _104196 s t s' t') = (term8 _104190 _104196 s s' t t')).
Proof. exact (eq_refl (term6 _104190 _104196 s s' t t')). Qed.
Lemma lem4339170 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term9 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4339171 (p : Prop) (q : Prop) (p' : Prop) : term10 p q p'.
Proof. exact (fun q' : Prop => @lem4339170 p q p' q'). Qed.
Lemma lem4339172 (p : Prop) (q : Prop) : term11 p q.
Proof. exact (fun p' : Prop => @lem4339171 p q p'). Qed.
Lemma lem4339173 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) : term12 _104241 _104242 s t s' t'.
Proof. exact (@lem4339172 (term13 _104241 _104242 s s' t t') (term7 _104241 _104242 s t s' t')). Qed.
Lemma lem4339174 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) (p' : Prop) : term14 _104241 _104242 s t s' t' p'.
Proof. exact (@lem4339173 _104241 _104242 s t s' t' p'). Qed.
Lemma lem4339175 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) (p' : Prop) : (term14 _104241 _104242 s t s' t' p') = (term15 _104241 _104242 s t s' t' p').
Proof. exact (eq_refl (term14 _104241 _104242 s t s' t' p')). Qed.
Lemma lem4339176 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) (p' : Prop) : term15 _104241 _104242 s t s' t' p'.
Proof. exact (EQ_MP (@lem4339175 _104241 _104242 s t s' t' p') (@lem4339174 _104241 _104242 s t s' t' p')). Qed.
Lemma lem4339177 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) (p' : Prop) (q' : Prop) : term16 _104241 _104242 s t s' t' p' q'.
Proof. exact (@lem4339176 _104241 _104242 s t s' t' p' q'). Qed.
Lemma lem4339178 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) (p' : Prop) (q' : Prop) : (term16 _104241 _104242 s t s' t' p' q') = (term17 _104241 _104242 s t s' t' p' q').
Proof. exact (eq_refl (term16 _104241 _104242 s t s' t' p' q')). Qed.
Lemma lem4339179 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) (p' : Prop) (q' : Prop) : term17 _104241 _104242 s t s' t' p' q'.
Proof. exact (EQ_MP (@lem4339178 _104241 _104242 s t s' t' p' q') (@lem4339177 _104241 _104242 s t s' t' p' q')). Qed.
Lemma lem4339182 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) : (term13 _104241 _104242 s s' t t') = (term13 _104241 _104242 s s' t t').
Proof. exact (eq_refl (term13 _104241 _104242 s s' t t')). Qed.
Lemma lem4339183 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (q' : Prop) : term18 _104241 _104242 s s' t t' q'.
Proof. exact (@lem4339179 _104241 _104242 s t s' t' (term13 _104241 _104242 s s' t t') q'). Qed.
Lemma lem4339184 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (q' : Prop) : term19 _104241 _104242 s s' t t' q'.
Proof. exact (@lem4339183 _104241 _104242 s s' t t' q' (@lem4339182 _104241 _104242 s s' t t')). Qed.
Lemma lem4339185 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : term13 _104241 _104242 s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4339186 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : @SUBSET _104242 t t'.
Proof. exact (proj2 (@lem4339185 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339187 {_104242 : Type'} (t : _104242 -> Prop) (t' : _104242 -> Prop) : (@SUBSET _104242 t t') = ((@SUBSET _104242 t t') = True).
Proof. exact (@lem7 (@SUBSET _104242 t t')). Qed.
Lemma lem4339189 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : @SUBSET _104241 s s'.
Proof. exact (proj1 (@lem4339185 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339190 {_104241 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) : (@SUBSET _104241 s s') = ((@SUBSET _104241 s s') = True).
Proof. exact (@lem7 (@SUBSET _104241 s s')). Qed.
Lemma lem4339193 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term7 _104190 _104196 s t s' t') = (term8 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4339149 _104190 _104196 s s' t t') (@lem4339148 _104190 _104196 s s' t t')). Qed.
Lemma lem4339194 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) : (term7 _104241 _104242 s t s' t') = (term8 _104241 _104242 s s' t t').
Proof. exact (@lem4339193 _104241 _104242 s s' t t'). Qed.
Lemma lem4339206 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (@SUBSET _104241 s s') = True.
Proof. exact (EQ_MP (@lem4339190 _104241 s s') (@lem4339189 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339208 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term20 _104241 s s') = (and True).
Proof. exact (MK_COMB (@lem4339207) (@lem4339206 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339210 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (@SUBSET _104242 t t') = True.
Proof. exact (EQ_MP (@lem4339187 _104242 t t') (@lem4339186 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339211 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term13 _104241 _104242 s s' t t') = (True /\ True).
Proof. exact (MK_COMB (@lem4339208 _104241 _104242 s s' t t' h1) (@lem4339210 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339213 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4339214 : (True /\ True) = True.
Proof. exact (@lem4339213 True). Qed.
Lemma lem4339215 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term13 _104241 _104242 s s' t t') = True.
Proof. exact (TRANS (@lem4339211 _104241 _104242 s s' t t' h1) (@lem4339214)). Qed.
Lemma lem4339216 {_104242 : Type'} (t : _104242 -> Prop) : (term21 _104242 t) = (term21 _104242 t).
Proof. exact (eq_refl (term21 _104242 t)). Qed.
Lemma lem4339217 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term22 _104241 _104242 s s' t t') = (term23 _104242 t).
Proof. exact (MK_COMB (@lem4339216 _104242 t) (@lem4339215 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339219 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4339220 {_104242 : Type'} (t : _104242 -> Prop) : (term23 _104242 t) = True.
Proof. exact (@lem4339219 (t = (@EMPTY _104242))). Qed.
Lemma lem4339221 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term22 _104241 _104242 s s' t t') = True.
Proof. exact (TRANS (@lem4339217 _104241 _104242 s s' t t' h1) (@lem4339220 _104242 t)). Qed.
Lemma lem4339222 {_104241 : Type'} (s : _104241 -> Prop) : (term21 _104241 s) = (term21 _104241 s).
Proof. exact (eq_refl (term21 _104241 s)). Qed.
Lemma lem4339223 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term8 _104241 _104242 s s' t t') = (term23 _104241 s).
Proof. exact (MK_COMB (@lem4339222 _104241 s) (@lem4339221 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339225 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4339226 {_104241 : Type'} (s : _104241 -> Prop) : (term23 _104241 s) = True.
Proof. exact (@lem4339225 (s = (@EMPTY _104241))). Qed.
Lemma lem4339227 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term8 _104241 _104242 s s' t t') = True.
Proof. exact (TRANS (@lem4339223 _104241 _104242 s s' t t' h1) (@lem4339226 _104241 s)). Qed.
Lemma lem4339228 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) (h1 : term13 _104241 _104242 s s' t t') : (term7 _104241 _104242 s t s' t') = True.
Proof. exact (TRANS (@lem4339194 _104241 _104242 s s' t t') (@lem4339227 _104241 _104242 s s' t t' h1)). Qed.
Lemma lem4339229 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) : term24 _104241 _104242 s t s' t'.
Proof. exact (fun h0 : term13 _104241 _104242 s s' t t' => @lem4339228 _104241 _104242 s s' t t' h0). Qed.
Lemma lem4339230 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) : term25 _104241 _104242 s s' t t'.
Proof. exact (@lem4339184 _104241 _104242 s s' t t' True). Qed.
Lemma lem4339231 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) : (term26 _104241 _104242 s t s' t') = (term27 _104241 _104242 s s' t t').
Proof. exact (@lem4339230 _104241 _104242 s s' t t' (@lem4339229 _104241 _104242 s t s' t')). Qed.
Lemma lem4339233 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4339234 {_104241 _104242 : Type'} (s : _104241 -> Prop) (s' : _104241 -> Prop) (t : _104242 -> Prop) (t' : _104242 -> Prop) : (term27 _104241 _104242 s s' t t') = True.
Proof. exact (@lem4339233 (term13 _104241 _104242 s s' t t')). Qed.
Lemma lem4339235 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) (t' : _104242 -> Prop) : (term26 _104241 _104242 s t s' t') = True.
Proof. exact (TRANS (@lem4339231 _104241 _104242 s s' t t') (@lem4339234 _104241 _104242 s s' t t')). Qed.
Lemma lem4339236 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) : (term28 _104241 _104242 s t s') = (term29 _104242).
Proof. exact (fun_ext (fun t' : _104242 -> Prop => @lem4339235 _104241 _104242 s t s' t')). Qed.
Lemma lem4339237 {_104242 : Type'} : (@all (_104242 -> Prop)) = (@all (_104242 -> Prop)).
Proof. exact (eq_refl (@all (_104242 -> Prop))). Qed.
Lemma lem4339238 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) : (term30 _104241 _104242 s t s') = (term31 _104242).
Proof. exact (MK_COMB (@lem4339237 _104242) (@lem4339236 _104241 _104242 s t s')). Qed.
Lemma lem4339240 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4339241 {_104242 : Type'} (t : Prop) : (term33 _104242 t) = t.
Proof. exact (@lem4339240 (_104242 -> Prop) t). Qed.
Lemma lem4339242 {_104242 : Type'} : (term31 _104242) = True.
Proof. exact (@lem4339241 _104242 True). Qed.
Lemma lem4339243 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) (s' : _104241 -> Prop) : (term30 _104241 _104242 s t s') = True.
Proof. exact (TRANS (@lem4339238 _104241 _104242 s t s') (@lem4339242 _104242)). Qed.
Lemma lem4339244 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) : (term34 _104241 _104242 s t) = (term29 _104241).
Proof. exact (fun_ext (fun s' : _104241 -> Prop => @lem4339243 _104241 _104242 s t s')). Qed.
Lemma lem4339245 {_104241 : Type'} : (@all (_104241 -> Prop)) = (@all (_104241 -> Prop)).
Proof. exact (eq_refl (@all (_104241 -> Prop))). Qed.
Lemma lem4339246 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) : (term35 _104241 _104242 s t) = (term31 _104241).
Proof. exact (MK_COMB (@lem4339245 _104241) (@lem4339244 _104241 _104242 s t)). Qed.
Lemma lem4339248 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4339249 {_104241 : Type'} (t : Prop) : (term33 _104241 t) = t.
Proof. exact (@lem4339248 (_104241 -> Prop) t). Qed.
Lemma lem4339250 {_104241 : Type'} : (term31 _104241) = True.
Proof. exact (@lem4339249 _104241 True). Qed.
Lemma lem4339251 {_104241 _104242 : Type'} (s : _104241 -> Prop) (t : _104242 -> Prop) : (term35 _104241 _104242 s t) = True.
Proof. exact (TRANS (@lem4339246 _104241 _104242 s t) (@lem4339250 _104241)). Qed.
Lemma lem4339252 {_104241 _104242 : Type'} (s : _104241 -> Prop) : (term36 _104241 _104242 s) = (term29 _104242).
Proof. exact (fun_ext (fun t : _104242 -> Prop => @lem4339251 _104241 _104242 s t)). Qed.
Lemma lem4339253 {_104242 : Type'} : (@all (_104242 -> Prop)) = (@all (_104242 -> Prop)).
Proof. exact (eq_refl (@all (_104242 -> Prop))). Qed.
Lemma lem4339254 {_104241 _104242 : Type'} (s : _104241 -> Prop) : (term37 _104241 _104242 s) = (term31 _104242).
Proof. exact (MK_COMB (@lem4339253 _104242) (@lem4339252 _104241 _104242 s)). Qed.
Lemma lem4339256 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4339257 {_104242 : Type'} (t : Prop) : (term33 _104242 t) = t.
Proof. exact (@lem4339256 (_104242 -> Prop) t). Qed.
Lemma lem4339258 {_104242 : Type'} : (term31 _104242) = True.
Proof. exact (@lem4339257 _104242 True). Qed.
Lemma lem4339259 {_104241 _104242 : Type'} (s : _104241 -> Prop) : (term37 _104241 _104242 s) = True.
Proof. exact (TRANS (@lem4339254 _104241 _104242 s) (@lem4339258 _104242)). Qed.
Lemma lem4339260 {_104241 _104242 : Type'} : (term38 _104241 _104242) = (term29 _104241).
Proof. exact (fun_ext (fun s : _104241 -> Prop => @lem4339259 _104241 _104242 s)). Qed.
Lemma lem4339261 {_104241 : Type'} : (@all (_104241 -> Prop)) = (@all (_104241 -> Prop)).
Proof. exact (eq_refl (@all (_104241 -> Prop))). Qed.
Lemma lem4339262 {_104241 _104242 : Type'} : (term39 _104241 _104242) = (term31 _104241).
Proof. exact (MK_COMB (@lem4339261 _104241) (@lem4339260 _104241 _104242)). Qed.
Lemma lem4339264 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4339265 {_104241 : Type'} (t : Prop) : (term33 _104241 t) = t.
Proof. exact (@lem4339264 (_104241 -> Prop) t). Qed.
Lemma lem4339266 {_104241 : Type'} : (term31 _104241) = True.
Proof. exact (@lem4339265 _104241 True). Qed.
Lemma lem4339267 {_104241 _104242 : Type'} : (term39 _104241 _104242) = True.
Proof. exact (TRANS (@lem4339262 _104241 _104242) (@lem4339266 _104241)). Qed.
Lemma lem4339268 {_104241 _104242 : Type'} : True = (term39 _104241 _104242).
Proof. exact (SYM (@lem4339267 _104241 _104242)). Qed.
Lemma lem4339269 {_104241 _104242 : Type'} : term39 _104241 _104242.
Proof. exact (EQ_MP (@lem4339268 _104241 _104242) (@lem0)). Qed.
