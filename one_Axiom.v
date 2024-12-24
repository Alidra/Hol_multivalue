Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import one_Axiom_term_abbrevs.
Require Import EXISTS_UNIQUE_THM_spec.
Require Import FUN_EQ_THM_spec.
Require Import one_spec.
Require Import one_RECURSION_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem16033 (v : unit) : term0 v.
Proof. exact (@lem15881 v). Qed.
Lemma lem16034 (v : unit) : (term0 v) = (v = tt).
Proof. exact (eq_refl (term0 v)). Qed.
Lemma lem16036 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem16037 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem16038 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem16037 A B f) (@lem16036 A B f)). Qed.
Lemma lem16039 {A B : Type'} (f : A -> B) (g : A -> B) : term3 A B f g.
Proof. exact (@lem16038 A B f g). Qed.
Lemma lem16040 {A B : Type'} (f : A -> B) (g : A -> B) : (term3 A B f g) = ((f = g) = (term4 A B f g)).
Proof. exact (eq_refl (term3 A B f g)). Qed.
Lemma lem16042 {A : Type'} (e : A) : term5 A e.
Proof. exact (@lem16032 A e). Qed.
Lemma lem16043 {A : Type'} (e : A) : (term5 A e) = (term6 A e).
Proof. exact (eq_refl (term5 A e)). Qed.
Lemma lem16044 {A : Type'} (e : A) : term6 A e.
Proof. exact (EQ_MP (@lem16043 A e) (@lem16042 A e)). Qed.
Lemma lem16045 {A : Type'} (e : A) : (term6 A e) = ((term6 A e) = True).
Proof. exact (@lem7 (term6 A e)). Qed.
Lemma lem16047 {A : Type'} (P : A -> Prop) : term7 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem16048 {A : Type'} (P : A -> Prop) : (term7 A P) = ((term8 A P) = (term9 A P)).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem16051 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (EQ_MP (@lem16048 A P) (@lem16047 A P)). Qed.
Lemma lem16052 {A : Type'} (P : type388 A) : (term10 A P) = (term11 A P).
Proof. exact (@lem16051 (unit -> A) P). Qed.
Lemma lem16053 {A : Type'} (e : A) : (term12 A e) = (term13 A e).
Proof. exact (@lem16052 A (term14 A e)). Qed.
Lemma lem16054 {A : Type'} (fn : unit -> A) (e : A) : (term15 A e fn) = ((fn tt) = e).
Proof. exact (eq_refl (term15 A e fn)). Qed.
Lemma lem16055 {A : Type'} (e : A) : (term16 A e) = (term14 A e).
Proof. exact (fun_ext (fun fn : unit -> A => @lem16054 A fn e)). Qed.
Lemma lem16056 {A : Type'} : (@ex1 (unit -> A)) = (@ex1 (unit -> A)).
Proof. exact (eq_refl (@ex1 (unit -> A))). Qed.
Lemma lem16057 {A : Type'} (e : A) : (term12 A e) = (term17 A e).
Proof. exact (MK_COMB (@lem16056 A) (@lem16055 A e)). Qed.
Lemma lem16058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16059 {A : Type'} (e : A) : (term18 A e) = (term19 A e).
Proof. exact (MK_COMB (@lem16058) (@lem16057 A e)). Qed.
Lemma lem16060 {A : Type'} (fn : unit -> A) (e : A) : (term15 A e fn) = ((fn tt) = e).
Proof. exact (eq_refl (term15 A e fn)). Qed.
Lemma lem16061 {A : Type'} (e : A) : (term16 A e) = (term14 A e).
Proof. exact (fun_ext (fun fn : unit -> A => @lem16060 A fn e)). Qed.
Lemma lem16062 {A : Type'} : (@ex (unit -> A)) = (@ex (unit -> A)).
Proof. exact (eq_refl (@ex (unit -> A))). Qed.
Lemma lem16063 {A : Type'} (e : A) : (term20 A e) = (term6 A e).
Proof. exact (MK_COMB (@lem16062 A) (@lem16061 A e)). Qed.
Lemma lem16064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem16065 {A : Type'} (e : A) : (term21 A e) = (term22 A e).
Proof. exact (MK_COMB (@lem16064) (@lem16063 A e)). Qed.
Lemma lem16066 {A : Type'} (fn : unit -> A) (e : A) : (term15 A e fn) = ((fn tt) = e).
Proof. exact (eq_refl (term15 A e fn)). Qed.
Lemma lem16067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem16068 {A : Type'} (fn : unit -> A) (e : A) : (term23 A e fn) = (term24 A fn e).
Proof. exact (MK_COMB (@lem16067) (@lem16066 A fn e)). Qed.
Lemma lem16069 {A : Type'} (x' : unit -> A) (e : A) : (term15 A e x') = ((x' tt) = e).
Proof. exact (eq_refl (term15 A e x')). Qed.
Lemma lem16070 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) : (term25 A fn e x') = (term26 A fn x' e).
Proof. exact (MK_COMB (@lem16068 A fn e) (@lem16069 A x' e)). Qed.
Lemma lem16071 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem16072 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) : (term27 A fn e x') = (term28 A fn x' e).
Proof. exact (MK_COMB (@lem16071) (@lem16070 A fn x' e)). Qed.
Lemma lem16073 {A : Type'} (fn : unit -> A) (x' : unit -> A) : (fn = x') = (fn = x').
Proof. exact (eq_refl (fn = x')). Qed.
Lemma lem16074 {A : Type'} (e : A) (fn : unit -> A) (x' : unit -> A) : (term29 A e fn x') = (term30 A e fn x').
Proof. exact (MK_COMB (@lem16072 A fn x' e) (@lem16073 A fn x')). Qed.
Lemma lem16075 {A : Type'} (e : A) (fn : unit -> A) : (term31 A e fn) = (term32 A e fn).
Proof. exact (fun_ext (fun x' : unit -> A => @lem16074 A e fn x')). Qed.
Lemma lem16076 {A : Type'} : (@all (unit -> A)) = (@all (unit -> A)).
Proof. exact (eq_refl (@all (unit -> A))). Qed.
Lemma lem16077 {A : Type'} (e : A) (fn : unit -> A) : (term33 A e fn) = (term34 A e fn).
Proof. exact (MK_COMB (@lem16076 A) (@lem16075 A e fn)). Qed.
Lemma lem16078 {A : Type'} (e : A) : (term35 A e) = (term36 A e).
Proof. exact (fun_ext (fun fn : unit -> A => @lem16077 A e fn)). Qed.
Lemma lem16079 {A : Type'} : (@all (unit -> A)) = (@all (unit -> A)).
Proof. exact (eq_refl (@all (unit -> A))). Qed.
Lemma lem16080 {A : Type'} (e : A) : (term37 A e) = (term38 A e).
Proof. exact (MK_COMB (@lem16079 A) (@lem16078 A e)). Qed.
Lemma lem16081 {A : Type'} (e : A) : (term13 A e) = (term39 A e).
Proof. exact (MK_COMB (@lem16065 A e) (@lem16080 A e)). Qed.
Lemma lem16082 {A : Type'} (e : A) : ((term12 A e) = (term13 A e)) = ((term17 A e) = (term39 A e)).
Proof. exact (MK_COMB (@lem16059 A e) (@lem16081 A e)). Qed.
Lemma lem16083 {A : Type'} (e : A) : (term17 A e) = (term39 A e).
Proof. exact (EQ_MP (@lem16082 A e) (@lem16053 A e)). Qed.
Lemma lem16087 {A : Type'} (e : A) : (term6 A e) = True.
Proof. exact (EQ_MP (@lem16045 A e) (@lem16044 A e)). Qed.
Lemma lem16088 {A : Type'} (e : A) : (term6 A e) = True.
Proof. exact (@lem16087 A e). Qed.
Lemma lem16089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem16090 {A : Type'} (e : A) : (term22 A e) = (and True).
Proof. exact (MK_COMB (@lem16089) (@lem16088 A e)). Qed.
Lemma lem16109 {A : Type'} (e : A) : (term38 A e) = (term38 A e).
Proof. exact (eq_refl (term38 A e)). Qed.
Lemma lem16110 {A : Type'} (e : A) : (term39 A e) = (term40 A e).
Proof. exact (MK_COMB (@lem16090 A e) (@lem16109 A e)). Qed.
Lemma lem16112 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem16113 {A : Type'} (e : A) : (term40 A e) = (term38 A e).
Proof. exact (@lem16112 (term38 A e)). Qed.
Lemma lem16132 {A : Type'} (e : A) : (term39 A e) = (term38 A e).
Proof. exact (TRANS (@lem16110 A e) (@lem16113 A e)). Qed.
Lemma lem16133 {A : Type'} (e : A) : (term17 A e) = (term38 A e).
Proof. exact (TRANS (@lem16083 A e) (@lem16132 A e)). Qed.
Lemma lem16134 {A : Type'} (e : A) : (term38 A e) = (term17 A e).
Proof. exact (SYM (@lem16133 A e)). Qed.
Lemma lem16135 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : term26 A fn x' e) : term26 A fn x' e.
Proof. exact (h1). Qed.
Lemma lem16136 {A : Type'} (x' : unit -> A) (e : A) (h1 : (x' tt) = e) : (x' tt) = e.
Proof. exact (h1). Qed.
Lemma lem16137 {A : Type'} (fn : unit -> A) (e : A) (h1 : (fn tt) = e) : (fn tt) = e.
Proof. exact (h1). Qed.
Lemma lem16141 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term4 A B f g).
Proof. exact (EQ_MP (@lem16040 A B f g) (@lem16039 A B f g)). Qed.
Lemma lem16142 {A : Type'} (f : unit -> A) (g : unit -> A) : (f = g) = (term41 A f g).
Proof. exact (@lem16141 unit A f g). Qed.
Lemma lem16143 {A : Type'} (fn : unit -> A) (x' : unit -> A) : (fn = x') = (term41 A fn x').
Proof. exact (@lem16142 A fn x'). Qed.
Lemma lem16144 {A : Type'} (fn : unit -> A) (x' : unit -> A) : (term41 A fn x') = (fn = x').
Proof. exact (SYM (@lem16143 A fn x')). Qed.
Lemma lem16168 (v : unit) : v = tt.
Proof. exact (EQ_MP (@lem16034 v) (@lem16033 v)). Qed.
Lemma lem16169 (x : unit) : x = tt.
Proof. exact (@lem16168 x). Qed.
Lemma lem16170 {A : Type'} (fn : unit -> A) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem16171 {A : Type'} (x : unit) (fn : unit -> A) : (fn x) = (fn tt).
Proof. exact (MK_COMB (@lem16170 A fn) (@lem16169 x)). Qed.
Lemma lem16172 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem16173 {A : Type'} (x : unit) (fn : unit -> A) : (term42 A fn x) = (term43 A fn).
Proof. exact (MK_COMB (@lem16172 A) (@lem16171 A x fn)). Qed.
Lemma lem16179 (v : unit) : v = tt.
Proof. exact (EQ_MP (@lem16034 v) (@lem16033 v)). Qed.
Lemma lem16180 (x : unit) : x = tt.
Proof. exact (@lem16179 x). Qed.
Lemma lem16181 {A : Type'} (x' : unit -> A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem16182 {A : Type'} (x : unit) (x' : unit -> A) : (x' x) = (x' tt).
Proof. exact (MK_COMB (@lem16181 A x') (@lem16180 x)). Qed.
Lemma lem16183 {A : Type'} (x : unit) (fn : unit -> A) (x' : unit -> A) : ((fn x) = (x' x)) = ((fn tt) = (x' tt)).
Proof. exact (MK_COMB (@lem16173 A x fn) (@lem16182 A x x')). Qed.
Lemma lem16184 {A : Type'} (fn : unit -> A) (x' : unit -> A) : (term44 A fn x') = (term45 A fn x').
Proof. exact (fun_ext (fun x : unit => @lem16183 A x fn x')). Qed.
Lemma lem16185 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem16186 {A : Type'} (fn : unit -> A) (x' : unit -> A) : (term41 A fn x') = (term46 A fn x').
Proof. exact (MK_COMB (@lem16185) (@lem16184 A fn x')). Qed.
Lemma lem16187 {A : Type'} (fn : unit -> A) (x' : unit -> A) : (term46 A fn x') = (term41 A fn x').
Proof. exact (SYM (@lem16186 A fn x')). Qed.
Lemma lem16189 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem16190 (t : Prop) : (term48 t) = t.
Proof. exact (@lem16189 unit t). Qed.
Lemma lem16191 {A : Type'} (fn : unit -> A) (x' : unit -> A) : (term46 A fn x') = ((fn tt) = (x' tt)).
Proof. exact (@lem16190 ((fn tt) = (x' tt))). Qed.
Lemma lem16195 {A : Type'} (fn : unit -> A) (e : A) (h1 : (fn tt) = e) : (fn tt) = e.
Proof. exact (h1). Qed.
Lemma lem16196 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem16197 {A : Type'} (fn : unit -> A) (e : A) (h1 : (fn tt) = e) : (term43 A fn) = (@eq A e).
Proof. exact (MK_COMB (@lem16196 A) (@lem16195 A fn e h1)). Qed.
Lemma lem16199 {A : Type'} (x' : unit -> A) (e : A) (h1 : (x' tt) = e) : (x' tt) = e.
Proof. exact (h1). Qed.
Lemma lem16200 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : ((fn tt) = (x' tt)) = (e = e).
Proof. exact (MK_COMB (@lem16197 A fn e h1) (@lem16199 A x' e h2)). Qed.
Lemma lem16202 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem16203 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem16202 A x). Qed.
Lemma lem16204 {A : Type'} (e : A) : (e = e) = True.
Proof. exact (@lem16203 A e). Qed.
Lemma lem16205 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : ((fn tt) = (x' tt)) = True.
Proof. exact (TRANS (@lem16200 A fn x' e h1 h2) (@lem16204 A e)). Qed.
Lemma lem16206 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : (term46 A fn x') = True.
Proof. exact (TRANS (@lem16191 A fn x') (@lem16205 A fn x' e h1 h2)). Qed.
Lemma lem16207 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : True = (term46 A fn x').
Proof. exact (SYM (@lem16206 A fn x' e h1 h2)). Qed.
Lemma lem16208 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : term46 A fn x'.
Proof. exact (EQ_MP (@lem16207 A fn x' e h1 h2) (@lem0)). Qed.
Lemma lem16209 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : term41 A fn x'.
Proof. exact (EQ_MP (@lem16187 A fn x') (@lem16208 A fn x' e h1 h2)). Qed.
Lemma lem16210 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : fn = x'.
Proof. exact (EQ_MP (@lem16144 A fn x') (@lem16209 A fn x' e h1 h2)). Qed.
Lemma lem16211 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : term26 A fn x' e) : (x' tt) = e.
Proof. exact (proj2 (@lem16135 A fn x' e h1)). Qed.
Lemma lem16212 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : term26 A fn x' e) : (fn tt) = e.
Proof. exact (proj1 (@lem16135 A fn x' e h1)). Qed.
Lemma lem16213 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : ((x' tt) = e) = (fn = x').
Proof. exact (prop_ext (fun h3 : (x' tt) = e => @lem16210 A fn x' e h1 h2) (fun h3 : fn = x' => @lem16136 A x' e h2)). Qed.
Lemma lem16214 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : fn = x'.
Proof. exact (EQ_MP (@lem16213 A fn x' e h1 h2) (@lem16136 A x' e h2)). Qed.
Lemma lem16215 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : ((fn tt) = e) = (fn = x').
Proof. exact (prop_ext (fun h3 : (fn tt) = e => @lem16214 A fn x' e h1 h2) (fun h3 : fn = x' => @lem16137 A fn e h1)). Qed.
Lemma lem16216 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : (fn tt) = e) (h2 : (x' tt) = e) : fn = x'.
Proof. exact (EQ_MP (@lem16215 A fn x' e h1 h2) (@lem16137 A fn e h1)). Qed.
Lemma lem16217 {A : Type'} (x' : unit -> A) (fn : unit -> A) (e : A) (h1 : term26 A fn x' e) (h2 : (fn tt) = e) : ((x' tt) = e) = (fn = x').
Proof. exact (prop_ext (fun h3 : (x' tt) = e => @lem16216 A fn x' e h2 h3) (fun h3 : fn = x' => @lem16211 A fn x' e h1)). Qed.
Lemma lem16218 {A : Type'} (x' : unit -> A) (fn : unit -> A) (e : A) (h1 : term26 A fn x' e) (h2 : (fn tt) = e) : fn = x'.
Proof. exact (EQ_MP (@lem16217 A x' fn e h1 h2) (@lem16211 A fn x' e h1)). Qed.
Lemma lem16219 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : term26 A fn x' e) : ((fn tt) = e) = (fn = x').
Proof. exact (prop_ext (fun h2 : (fn tt) = e => @lem16218 A x' fn e h1 h2) (fun h2 : fn = x' => @lem16212 A fn x' e h1)). Qed.
Lemma lem16220 {A : Type'} (fn : unit -> A) (x' : unit -> A) (e : A) (h1 : term26 A fn x' e) : fn = x'.
Proof. exact (EQ_MP (@lem16219 A fn x' e h1) (@lem16212 A fn x' e h1)). Qed.
Lemma lem16221 {A : Type'} (e : A) (fn : unit -> A) (x' : unit -> A) : term30 A e fn x'.
Proof. exact (fun h0 : term26 A fn x' e => @lem16220 A fn x' e h0). Qed.
Lemma lem16226 {A : Type'} (e : A) (fn : unit -> A) : term34 A e fn.
Proof. exact (fun x' : unit -> A => @lem16221 A e fn x'). Qed.
Lemma lem16231 {A : Type'} (e : A) : term38 A e.
Proof. exact (fun fn : unit -> A => @lem16226 A e fn). Qed.
Lemma lem16232 {A : Type'} (e : A) : term17 A e.
Proof. exact (EQ_MP (@lem16134 A e) (@lem16231 A e)). Qed.
Lemma lem16237 {A : Type'} : term49 A.
Proof. exact (fun e : A => @lem16232 A e). Qed.
