Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_OF_LIST_APPEND_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_SET_OF_LIST_spec.
Require Import IN_UNION_spec.
Require Import MEM_APPEND_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4790172 {_26945 : Type'} (x : _26945) : term0 _26945 x.
Proof. exact (@lem1145802 _26945 x). Qed.
Lemma lem4790173 {_26945 : Type'} (x : _26945) : (term0 _26945 x) = (term1 _26945 x).
Proof. exact (eq_refl (term0 _26945 x)). Qed.
Lemma lem4790174 {_26945 : Type'} (x : _26945) : term1 _26945 x.
Proof. exact (EQ_MP (@lem4790173 _26945 x) (@lem4790172 _26945 x)). Qed.
Lemma lem4790175 {_26945 : Type'} (x : _26945) (l1 : list _26945) : term2 _26945 x l1.
Proof. exact (@lem4790174 _26945 x l1). Qed.
Lemma lem4790176 {_26945 : Type'} (l1 : list _26945) (x : _26945) : (term2 _26945 x l1) = (term3 _26945 l1 x).
Proof. exact (eq_refl (term2 _26945 x l1)). Qed.
Lemma lem4790177 {_26945 : Type'} (l1 : list _26945) (x : _26945) : term3 _26945 l1 x.
Proof. exact (EQ_MP (@lem4790176 _26945 l1 x) (@lem4790175 _26945 x l1)). Qed.
Lemma lem4790178 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : term4 _26945 l1 x l2.
Proof. exact (@lem4790177 _26945 l1 x l2). Qed.
Lemma lem4790179 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : (term4 _26945 l1 x l2) = ((term5 _26945 x l1 l2) = (term6 _26945 l1 x l2)).
Proof. exact (eq_refl (term4 _26945 l1 x l2)). Qed.
Lemma lem4790181 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem4790182 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem4790183 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem4790182 A s) (@lem4790181 A s)). Qed.
Lemma lem4790184 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem4790183 A s t). Qed.
Lemma lem4790185 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term10 A s t).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem4790186 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (EQ_MP (@lem4790185 A s t) (@lem4790184 A s t)). Qed.
Lemma lem4790187 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term11 A s t x.
Proof. exact (@lem4790186 A s t x). Qed.
Lemma lem4790188 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s t x) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl (term11 A s t x)). Qed.
Lemma lem4790190 {_110384 : Type'} (x : _110384) : term14 _110384 x.
Proof. exact (@lem4790171 _110384 x). Qed.
Lemma lem4790191 {_110384 : Type'} (x : _110384) : (term14 _110384 x) = (term15 _110384 x).
Proof. exact (eq_refl (term14 _110384 x)). Qed.
Lemma lem4790192 {_110384 : Type'} (x : _110384) : term15 _110384 x.
Proof. exact (EQ_MP (@lem4790191 _110384 x) (@lem4790190 _110384 x)). Qed.
Lemma lem4790193 {_110384 : Type'} (x : _110384) (l : list _110384) : term16 _110384 x l.
Proof. exact (@lem4790192 _110384 x l). Qed.
Lemma lem4790194 {_110384 : Type'} (x : _110384) (l : list _110384) : (term16 _110384 x l) = ((term17 _110384 x l) = (@List.In _110384 x l)).
Proof. exact (eq_refl (term16 _110384 x l)). Qed.
Lemma lem4790196 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4790197 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem4790198 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (EQ_MP (@lem4790197 A s) (@lem4790196 A s)). Qed.
Lemma lem4790199 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term20 A s t.
Proof. exact (@lem4790198 A s t). Qed.
Lemma lem4790200 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = ((s = t) = (term21 A s t)).
Proof. exact (eq_refl (term20 A s t)). Qed.
Lemma lem4790213 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem4790200 A s t) (@lem4790199 A s t)). Qed.
Lemma lem4790214 {_110409 : Type'} (s : _110409 -> Prop) (t : _110409 -> Prop) : (s = t) = (term21 _110409 s t).
Proof. exact (@lem4790213 _110409 s t). Qed.
Lemma lem4790215 {_110409 : Type'} (l1 : list _110409) (l2 : list _110409) : ((term22 _110409 l1 l2) = (term23 _110409 l1 l2)) = (term24 _110409 l1 l2).
Proof. exact (@lem4790214 _110409 (term22 _110409 l1 l2) (term23 _110409 l1 l2)). Qed.
Lemma lem4790225 {_110384 : Type'} (x : _110384) (l : list _110384) : (term17 _110384 x l) = (@List.In _110384 x l).
Proof. exact (EQ_MP (@lem4790194 _110384 x l) (@lem4790193 _110384 x l)). Qed.
Lemma lem4790226 {_110409 : Type'} (x : _110409) (l : list _110409) : (term17 _110409 x l) = (@List.In _110409 x l).
Proof. exact (@lem4790225 _110409 x l). Qed.
Lemma lem4790227 {_110409 : Type'} (x : _110409) (l1 : list _110409) (l2 : list _110409) : (term25 _110409 x l1 l2) = (term5 _110409 x l1 l2).
Proof. exact (@lem4790226 _110409 x (@List.app _110409 l1 l2)). Qed.
Lemma lem4790229 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : (term5 _26945 x l1 l2) = (term6 _26945 l1 x l2).
Proof. exact (EQ_MP (@lem4790179 _26945 l1 x l2) (@lem4790178 _26945 l1 x l2)). Qed.
Lemma lem4790230 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : (term5 _110409 x l1 l2) = (term6 _110409 l1 x l2).
Proof. exact (@lem4790229 _110409 l1 x l2). Qed.
Lemma lem4790233 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : (term25 _110409 x l1 l2) = (term6 _110409 l1 x l2).
Proof. exact (TRANS (@lem4790227 _110409 x l1 l2) (@lem4790230 _110409 l1 x l2)). Qed.
Lemma lem4790234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4790235 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : (term26 _110409 x l1 l2) = (term27 _110409 l1 x l2).
Proof. exact (MK_COMB (@lem4790234) (@lem4790233 _110409 l1 x l2)). Qed.
Lemma lem4790237 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem4790188 A s x t) (@lem4790187 A s t x)). Qed.
Lemma lem4790238 {_110409 : Type'} (s : _110409 -> Prop) (x : _110409) (t : _110409 -> Prop) : (term12 _110409 x s t) = (term13 _110409 s x t).
Proof. exact (@lem4790237 _110409 s x t). Qed.
Lemma lem4790239 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : (term28 _110409 x l1 l2) = (term29 _110409 l1 x l2).
Proof. exact (@lem4790238 _110409 (@set_of_list _110409 l1) x (@set_of_list _110409 l2)). Qed.
Lemma lem4790243 {_110384 : Type'} (x : _110384) (l : list _110384) : (term17 _110384 x l) = (@List.In _110384 x l).
Proof. exact (EQ_MP (@lem4790194 _110384 x l) (@lem4790193 _110384 x l)). Qed.
Lemma lem4790244 {_110409 : Type'} (x : _110409) (l : list _110409) : (term17 _110409 x l) = (@List.In _110409 x l).
Proof. exact (@lem4790243 _110409 x l). Qed.
Lemma lem4790245 {_110409 : Type'} (x : _110409) (l1 : list _110409) : (term17 _110409 x l1) = (@List.In _110409 x l1).
Proof. exact (@lem4790244 _110409 x l1). Qed.
Lemma lem4790246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4790247 {_110409 : Type'} (x : _110409) (l1 : list _110409) : (term30 _110409 x l1) = (term31 _110409 x l1).
Proof. exact (MK_COMB (@lem4790246) (@lem4790245 _110409 x l1)). Qed.
Lemma lem4790249 {_110384 : Type'} (x : _110384) (l : list _110384) : (term17 _110384 x l) = (@List.In _110384 x l).
Proof. exact (EQ_MP (@lem4790194 _110384 x l) (@lem4790193 _110384 x l)). Qed.
Lemma lem4790250 {_110409 : Type'} (x : _110409) (l : list _110409) : (term17 _110409 x l) = (@List.In _110409 x l).
Proof. exact (@lem4790249 _110409 x l). Qed.
Lemma lem4790251 {_110409 : Type'} (x : _110409) (l2 : list _110409) : (term17 _110409 x l2) = (@List.In _110409 x l2).
Proof. exact (@lem4790250 _110409 x l2). Qed.
Lemma lem4790252 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : (term29 _110409 l1 x l2) = (term6 _110409 l1 x l2).
Proof. exact (MK_COMB (@lem4790247 _110409 x l1) (@lem4790251 _110409 x l2)). Qed.
Lemma lem4790255 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : (term28 _110409 x l1 l2) = (term6 _110409 l1 x l2).
Proof. exact (TRANS (@lem4790239 _110409 l1 x l2) (@lem4790252 _110409 l1 x l2)). Qed.
Lemma lem4790256 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : ((term25 _110409 x l1 l2) = (term28 _110409 x l1 l2)) = ((term6 _110409 l1 x l2) = (term6 _110409 l1 x l2)).
Proof. exact (MK_COMB (@lem4790235 _110409 l1 x l2) (@lem4790255 _110409 l1 x l2)). Qed.
Lemma lem4790258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4790259 (x : Prop) : (x = x) = True.
Proof. exact (@lem4790258 Prop x). Qed.
Lemma lem4790260 {_110409 : Type'} (l1 : list _110409) (x : _110409) (l2 : list _110409) : ((term6 _110409 l1 x l2) = (term6 _110409 l1 x l2)) = True.
Proof. exact (@lem4790259 (term6 _110409 l1 x l2)). Qed.
Lemma lem4790261 {_110409 : Type'} (x : _110409) (l1 : list _110409) (l2 : list _110409) : ((term25 _110409 x l1 l2) = (term28 _110409 x l1 l2)) = True.
Proof. exact (TRANS (@lem4790256 _110409 l1 x l2) (@lem4790260 _110409 l1 x l2)). Qed.
Lemma lem4790262 {_110409 : Type'} (l1 : list _110409) (l2 : list _110409) : (term32 _110409 l1 l2) = (term33 _110409).
Proof. exact (fun_ext (fun x : _110409 => @lem4790261 _110409 x l1 l2)). Qed.
Lemma lem4790263 {_110409 : Type'} : (@all _110409) = (@all _110409).
Proof. exact (eq_refl (@all _110409)). Qed.
Lemma lem4790264 {_110409 : Type'} (l1 : list _110409) (l2 : list _110409) : (term24 _110409 l1 l2) = (term34 _110409).
Proof. exact (MK_COMB (@lem4790263 _110409) (@lem4790262 _110409 l1 l2)). Qed.
Lemma lem4790266 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4790267 {_110409 : Type'} (t : Prop) : (term35 _110409 t) = t.
Proof. exact (@lem4790266 _110409 t). Qed.
Lemma lem4790268 {_110409 : Type'} : (term34 _110409) = True.
Proof. exact (@lem4790267 _110409 True). Qed.
Lemma lem4790269 {_110409 : Type'} (l1 : list _110409) (l2 : list _110409) : (term24 _110409 l1 l2) = True.
Proof. exact (TRANS (@lem4790264 _110409 l1 l2) (@lem4790268 _110409)). Qed.
Lemma lem4790270 {_110409 : Type'} (l1 : list _110409) (l2 : list _110409) : ((term22 _110409 l1 l2) = (term23 _110409 l1 l2)) = True.
Proof. exact (TRANS (@lem4790215 _110409 l1 l2) (@lem4790269 _110409 l1 l2)). Qed.
Lemma lem4790271 {_110409 : Type'} (l1 : list _110409) : (term36 _110409 l1) = (term37 _110409).
Proof. exact (fun_ext (fun l2 : list _110409 => @lem4790270 _110409 l1 l2)). Qed.
Lemma lem4790272 {_110409 : Type'} : (@all (list _110409)) = (@all (list _110409)).
Proof. exact (eq_refl (@all (list _110409))). Qed.
Lemma lem4790273 {_110409 : Type'} (l1 : list _110409) : (term38 _110409 l1) = (term39 _110409).
Proof. exact (MK_COMB (@lem4790272 _110409) (@lem4790271 _110409 l1)). Qed.
Lemma lem4790275 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4790276 {_110409 : Type'} (t : Prop) : (term40 _110409 t) = t.
Proof. exact (@lem4790275 (list _110409) t). Qed.
Lemma lem4790277 {_110409 : Type'} : (term39 _110409) = True.
Proof. exact (@lem4790276 _110409 True). Qed.
Lemma lem4790278 {_110409 : Type'} (l1 : list _110409) : (term38 _110409 l1) = True.
Proof. exact (TRANS (@lem4790273 _110409 l1) (@lem4790277 _110409)). Qed.
Lemma lem4790279 {_110409 : Type'} : (term41 _110409) = (term37 _110409).
Proof. exact (fun_ext (fun l1 : list _110409 => @lem4790278 _110409 l1)). Qed.
Lemma lem4790280 {_110409 : Type'} : (@all (list _110409)) = (@all (list _110409)).
Proof. exact (eq_refl (@all (list _110409))). Qed.
Lemma lem4790281 {_110409 : Type'} : (term42 _110409) = (term39 _110409).
Proof. exact (MK_COMB (@lem4790280 _110409) (@lem4790279 _110409)). Qed.
Lemma lem4790283 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4790284 {_110409 : Type'} (t : Prop) : (term40 _110409 t) = t.
Proof. exact (@lem4790283 (list _110409) t). Qed.
Lemma lem4790285 {_110409 : Type'} : (term39 _110409) = True.
Proof. exact (@lem4790284 _110409 True). Qed.
Lemma lem4790286 {_110409 : Type'} : (term42 _110409) = True.
Proof. exact (TRANS (@lem4790281 _110409) (@lem4790285 _110409)). Qed.
Lemma lem4790287 {_110409 : Type'} : True = (term42 _110409).
Proof. exact (SYM (@lem4790286 _110409)). Qed.
Lemma lem4790288 {_110409 : Type'} : term42 _110409.
Proof. exact (EQ_MP (@lem4790287 _110409) (@lem0)). Qed.
