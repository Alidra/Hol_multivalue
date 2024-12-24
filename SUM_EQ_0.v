Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_EQ_0_term_abbrevs.
Require Import ITERATE_EQ_NEUTRAL_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7069013 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7069015 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5804540 A B op). Qed.
Lemma lem7069016 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem7069017 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem7069016 A B op) (@lem7069015 A B op)). Qed.
Lemma lem7069018 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7069019 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term2 A B op.
Proof. exact (@lem7069017 A B op (@lem7069018 B op h1)). Qed.
Lemma lem7069020 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term3 A B op f.
Proof. exact (@lem7069019 A B op h1 f). Qed.
Lemma lem7069021 {A B : Type'} (f : A -> B) (op : type1400 B) : (term3 A B op f) = (term4 A B f op).
Proof. exact (eq_refl (term3 A B op f)). Qed.
Lemma lem7069022 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term4 A B f op.
Proof. exact (EQ_MP (@lem7069021 A B f op) (@lem7069020 A B f op h1)). Qed.
Lemma lem7069023 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term5 A B f op s.
Proof. exact (@lem7069022 A B f op h1 s). Qed.
Lemma lem7069024 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term5 A B f op s) = (term6 A B s f op).
Proof. exact (eq_refl (term5 A B f op s)). Qed.
Lemma lem7069025 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term6 A B s f op.
Proof. exact (EQ_MP (@lem7069024 A B s f op) (@lem7069023 A B f s op h1)). Qed.
Lemma lem7069026 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term7 A B s f op) : term7 A B s f op.
Proof. exact (h1). Qed.
Lemma lem7069027 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term7 A B s f op) (h2 : @monoidal B op) : (@iterate B A op s f) = (@neutral B op).
Proof. exact (@lem7069025 A B s f op h2 (@lem7069026 A B s f op h1)). Qed.
Lemma lem7069028 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term7 A B s f op) : term8 A B s f op.
Proof. exact (fun h0 : @monoidal B op => @lem7069027 A B s f op h1 h0). Qed.
Lemma lem7069029 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term9 A B s f op.
Proof. exact (fun h0 : term7 A B s f op => @lem7069028 A B s f op h0). Qed.
Lemma lem7069031 (p : Prop) (q : Prop) (r : Prop) : (term10 p q r) = (term11 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem7069036 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term9 A B s f op) = (term12 A B s f op).
Proof. exact (@lem7069031 (term7 A B s f op) (@monoidal B op) ((@iterate B A op s f) = (@neutral B op))). Qed.
Lemma lem7069038 (h1 : (@neutral real real_add) = term13) : (@neutral real real_add) = term13.
Proof. exact (h1). Qed.
Lemma lem7069039 (h1 : (@neutral real real_add) = term13) : term13 = (@neutral real real_add).
Proof. exact (SYM (@lem7069038 h1)). Qed.
Lemma lem7069040 (h1 : term13 = (@neutral real real_add)) : term13 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7069041 (h1 : term13 = (@neutral real real_add)) : (@neutral real real_add) = term13.
Proof. exact (SYM (@lem7069040 h1)). Qed.
Lemma lem7069042 : ((@neutral real real_add) = term13) = (term13 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term13 => @lem7069039 h1) (fun h1 : term13 = (@neutral real real_add) => @lem7069041 h1)). Qed.
Lemma lem7069063 : term13 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7069042) (@lem7065438)). Qed.
Lemma lem7069064 {A : Type'} (f : A -> real) (x : A) : (term14 A f x) = (term14 A f x).
Proof. exact (eq_refl (term14 A f x)). Qed.
Lemma lem7069065 {A : Type'} (f : A -> real) (x : A) : ((f x) = term13) = ((f x) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7069064 A f x) (@lem7069063)). Qed.
Lemma lem7069068 {A : Type'} (x : A) (s : A -> Prop) : (term15 A x s) = (term15 A x s).
Proof. exact (eq_refl (term15 A x s)). Qed.
Lemma lem7069069 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term16 A s f x) = (term17 A s f x).
Proof. exact (MK_COMB (@lem7069068 A x s) (@lem7069065 A f x)). Qed.
Lemma lem7069072 {A : Type'} (s : A -> Prop) (f : A -> real) : (term18 A s f) = (term19 A s f).
Proof. exact (fun_ext (fun x : A => @lem7069069 A s f x)). Qed.
Lemma lem7069073 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7069074 {A : Type'} (s : A -> Prop) (f : A -> real) : (term20 A s f) = (term21 A s f).
Proof. exact (MK_COMB (@lem7069073 A) (@lem7069072 A s f)). Qed.
Lemma lem7069079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7069080 {A : Type'} (s : A -> Prop) (f : A -> real) : (term22 A s f) = (term23 A s f).
Proof. exact (MK_COMB (@lem7069079) (@lem7069074 A s f)). Qed.
Lemma lem7069084 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7069085 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7069084 A). Qed.
Lemma lem7069086 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7069087 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7069085 A) (@lem7069086 A s)). Qed.
Lemma lem7069088 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7069089 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@iterate real A real_add s f).
Proof. exact (MK_COMB (@lem7069087 A s) (@lem7069088 A f)). Qed.
Lemma lem7069090 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069091 {A : Type'} (s : A -> Prop) (f : A -> real) : (term24 A s f) = (term25 A s f).
Proof. exact (MK_COMB (@lem7069090) (@lem7069089 A s f)). Qed.
Lemma lem7069093 : term13 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7069042) (@lem7065438)). Qed.
Lemma lem7069094 {A : Type'} (s : A -> Prop) (f : A -> real) : ((@sum A s f) = term13) = ((@iterate real A real_add s f) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7069091 A s f) (@lem7069093)). Qed.
Lemma lem7069097 {A : Type'} (s : A -> Prop) (f : A -> real) : (term26 A s f) = (term27 A s f).
Proof. exact (MK_COMB (@lem7069080 A s f) (@lem7069094 A s f)). Qed.
Lemma lem7069100 {A : Type'} (f : A -> real) : (term28 A f) = (term29 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7069097 A s f)). Qed.
Lemma lem7069101 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7069102 {A : Type'} (f : A -> real) : (term30 A f) = (term31 A f).
Proof. exact (MK_COMB (@lem7069101 A) (@lem7069100 A f)). Qed.
Lemma lem7069107 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7069102 A f)). Qed.
Lemma lem7069108 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7069109 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem7069108 A) (@lem7069107 A)). Qed.
Lemma lem7069114 {A : Type'} : (term35 A) = (term34 A).
Proof. exact (SYM (@lem7069109 A)). Qed.
Lemma lem7069126 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term36 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7069127 (p : Prop) (q : Prop) (p' : Prop) : term37 p q p'.
Proof. exact (fun q' : Prop => @lem7069126 p q p' q'). Qed.
Lemma lem7069128 (p : Prop) (q : Prop) : term38 p q.
Proof. exact (fun p' : Prop => @lem7069127 p q p'). Qed.
Lemma lem7069129 {A : Type'} (s : A -> Prop) (f : A -> real) : term39 A s f.
Proof. exact (@lem7069128 (term21 A s f) ((@iterate real A real_add s f) = (@neutral real real_add))). Qed.
Lemma lem7069130 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : term40 A s f p'.
Proof. exact (@lem7069129 A s f p'). Qed.
Lemma lem7069131 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : (term40 A s f p') = (term41 A s f p').
Proof. exact (eq_refl (term40 A s f p')). Qed.
Lemma lem7069132 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : term41 A s f p'.
Proof. exact (EQ_MP (@lem7069131 A s f p') (@lem7069130 A s f p')). Qed.
Lemma lem7069133 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term42 A s f p' q'.
Proof. exact (@lem7069132 A s f p' q'). Qed.
Lemma lem7069134 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term42 A s f p' q') = (term43 A s f p' q').
Proof. exact (eq_refl (term42 A s f p' q')). Qed.
Lemma lem7069135 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term43 A s f p' q'.
Proof. exact (EQ_MP (@lem7069134 A s f p' q') (@lem7069133 A s f p' q')). Qed.
Lemma lem7069167 {A : Type'} (s : A -> Prop) (f : A -> real) : (term21 A s f) = (term21 A s f).
Proof. exact (eq_refl (term21 A s f)). Qed.
Lemma lem7069168 {A : Type'} (s : A -> Prop) (f : A -> real) (q' : Prop) : term44 A s f q'.
Proof. exact (@lem7069135 A s f (term21 A s f) q'). Qed.
Lemma lem7069169 {A : Type'} (s : A -> Prop) (f : A -> real) (q' : Prop) : term45 A s f q'.
Proof. exact (@lem7069168 A s f q' (@lem7069167 A s f)). Qed.
Lemma lem7069170 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term21 A s f.
Proof. exact (h1). Qed.
Lemma lem7069171 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term46 A s f x.
Proof. exact (@lem7069170 A s f h1 x). Qed.
Lemma lem7069172 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term46 A s f x) = (term17 A s f x).
Proof. exact (eq_refl (term46 A s f x)). Qed.
Lemma lem7069173 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term17 A s f x.
Proof. exact (EQ_MP (@lem7069172 A s f x) (@lem7069171 A x s f h1)). Qed.
Lemma lem7069174 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7069175 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term21 A s f) (h2 : @IN A x s) : (f x) = (@neutral real real_add).
Proof. exact (@lem7069173 A x s f h1 (@lem7069174 A x s h2)). Qed.
Lemma lem7069184 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term12 A B s f op.
Proof. exact (EQ_MP (@lem7069036 A B s f op) (@lem7069029 A B s f op)). Qed.
Lemma lem7069185 {A : Type'} (s : A -> Prop) (f : A -> real) (op : type1627) : term47 A s f op.
Proof. exact (@lem7069184 A real s f op). Qed.
Lemma lem7069186 {A : Type'} (s : A -> Prop) (f : A -> real) : term48 A s f.
Proof. exact (@lem7069185 A s f real_add). Qed.
Lemma lem7069196 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term36 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7069197 (p : Prop) (q : Prop) (p' : Prop) : term37 p q p'.
Proof. exact (fun q' : Prop => @lem7069196 p q p' q'). Qed.
Lemma lem7069198 (p : Prop) (q : Prop) : term38 p q.
Proof. exact (fun p' : Prop => @lem7069197 p q p'). Qed.
Lemma lem7069199 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : term49 A s f x.
Proof. exact (@lem7069198 (@IN A x s) ((f x) = (@neutral real real_add))). Qed.
Lemma lem7069200 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term50 A s f x p'.
Proof. exact (@lem7069199 A s f x p'). Qed.
Lemma lem7069201 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term50 A s f x p') = (term51 A s f x p').
Proof. exact (eq_refl (term50 A s f x p')). Qed.
Lemma lem7069202 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term51 A s f x p'.
Proof. exact (EQ_MP (@lem7069201 A s f x p') (@lem7069200 A s f x p')). Qed.
Lemma lem7069203 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term52 A s f x p' q'.
Proof. exact (@lem7069202 A s f x p' q'). Qed.
Lemma lem7069204 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term52 A s f x p' q') = (term53 A s f x p' q').
Proof. exact (eq_refl (term52 A s f x p' q')). Qed.
Lemma lem7069205 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term53 A s f x p' q'.
Proof. exact (EQ_MP (@lem7069204 A s f x p' q') (@lem7069203 A s f x p' q')). Qed.
Lemma lem7069206 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7069207 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (q' : Prop) : term54 A f x s q'.
Proof. exact (@lem7069205 A s f x (@IN A x s) q'). Qed.
Lemma lem7069208 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (q' : Prop) : term55 A f x s q'.
Proof. exact (@lem7069207 A f x s q' (@lem7069206 A x s)). Qed.
Lemma lem7069209 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7069210 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7069215 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term17 A s f x.
Proof. exact (fun h0 : @IN A x s => @lem7069175 A f x s h1 h0). Qed.
Lemma lem7069216 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term17 A s f x.
Proof. exact (@lem7069215 A x s f h1). Qed.
Lemma lem7069218 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7069210 A x s) (@lem7069209 A x s h1)). Qed.
Lemma lem7069219 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem7069218 A x s h1)). Qed.
Lemma lem7069220 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem7069219 A x s h1) (@lem0)). Qed.
Lemma lem7069221 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term21 A s f) (h2 : @IN A x s) : (f x) = (@neutral real real_add).
Proof. exact (@lem7069216 A x s f h1 (@lem7069220 A x s h2)). Qed.
Lemma lem7069222 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069223 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term21 A s f) (h2 : @IN A x s) : (term14 A f x) = term56.
Proof. exact (MK_COMB (@lem7069222) (@lem7069221 A f x s h1 h2)). Qed.
Lemma lem7069224 : (@neutral real real_add) = (@neutral real real_add).
Proof. exact (eq_refl (@neutral real real_add)). Qed.
Lemma lem7069225 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term21 A s f) (h2 : @IN A x s) : ((f x) = (@neutral real real_add)) = ((@neutral real real_add) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7069223 A f x s h1 h2) (@lem7069224)). Qed.
Lemma lem7069227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7069228 (x : real) : (x = x) = True.
Proof. exact (@lem7069227 real x). Qed.
Lemma lem7069229 : ((@neutral real real_add) = (@neutral real real_add)) = True.
Proof. exact (@lem7069228 (@neutral real real_add)). Qed.
Lemma lem7069230 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term21 A s f) (h2 : @IN A x s) : ((f x) = (@neutral real real_add)) = True.
Proof. exact (TRANS (@lem7069225 A f x s h1 h2) (@lem7069229)). Qed.
Lemma lem7069231 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term57 A s f x.
Proof. exact (fun h0 : @IN A x s => @lem7069230 A f x s h1 h0). Qed.
Lemma lem7069232 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) : term58 A f x s.
Proof. exact (@lem7069208 A f x s True). Qed.
Lemma lem7069233 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term17 A s f x) = (term59 A x s).
Proof. exact (@lem7069232 A f x s (@lem7069231 A x s f h1)). Qed.
Lemma lem7069235 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7069236 {A : Type'} (x : A) (s : A -> Prop) : (term59 A x s) = True.
Proof. exact (@lem7069235 (@IN A x s)). Qed.
Lemma lem7069237 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term17 A s f x) = True.
Proof. exact (TRANS (@lem7069233 A x s f h1) (@lem7069236 A x s)). Qed.
Lemma lem7069238 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term19 A s f) = (term60 A).
Proof. exact (fun_ext (fun x : A => @lem7069237 A x s f h1)). Qed.
Lemma lem7069239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7069240 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term21 A s f) = (term61 A).
Proof. exact (MK_COMB (@lem7069239 A) (@lem7069238 A s f h1)). Qed.
Lemma lem7069242 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7069243 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (@lem7069242 A t). Qed.
Lemma lem7069244 {A : Type'} : (term61 A) = True.
Proof. exact (@lem7069243 A True). Qed.
Lemma lem7069245 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term21 A s f) = True.
Proof. exact (TRANS (@lem7069240 A s f h1) (@lem7069244 A)). Qed.
Lemma lem7069246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7069247 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term63 A s f) = (and True).
Proof. exact (MK_COMB (@lem7069246) (@lem7069245 A s f h1)). Qed.
Lemma lem7069249 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7069013) (@lem7067132)). Qed.
Lemma lem7069250 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term64 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem7069247 A s f h1) (@lem7069249)). Qed.
Lemma lem7069252 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7069253 : (True /\ True) = True.
Proof. exact (@lem7069252 True). Qed.
Lemma lem7069254 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term64 A s f) = True.
Proof. exact (TRANS (@lem7069250 A s f h1) (@lem7069253)). Qed.
Lemma lem7069255 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : True = (term64 A s f).
Proof. exact (SYM (@lem7069254 A s f h1)). Qed.
Lemma lem7069256 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term64 A s f.
Proof. exact (EQ_MP (@lem7069255 A s f h1) (@lem0)). Qed.
Lemma lem7069257 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (@iterate real A real_add s f) = (@neutral real real_add).
Proof. exact (@lem7069186 A s f (@lem7069256 A s f h1)). Qed.
Lemma lem7069258 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069259 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : (term25 A s f) = term56.
Proof. exact (MK_COMB (@lem7069258) (@lem7069257 A s f h1)). Qed.
Lemma lem7069260 : (@neutral real real_add) = (@neutral real real_add).
Proof. exact (eq_refl (@neutral real real_add)). Qed.
Lemma lem7069261 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : ((@iterate real A real_add s f) = (@neutral real real_add)) = ((@neutral real real_add) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7069259 A s f h1) (@lem7069260)). Qed.
Lemma lem7069263 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7069264 (x : real) : (x = x) = True.
Proof. exact (@lem7069263 real x). Qed.
Lemma lem7069265 : ((@neutral real real_add) = (@neutral real real_add)) = True.
Proof. exact (@lem7069264 (@neutral real real_add)). Qed.
Lemma lem7069266 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : ((@iterate real A real_add s f) = (@neutral real real_add)) = True.
Proof. exact (TRANS (@lem7069261 A s f h1) (@lem7069265)). Qed.
Lemma lem7069267 {A : Type'} (s : A -> Prop) (f : A -> real) : term65 A s f.
Proof. exact (fun h0 : term21 A s f => @lem7069266 A s f h0). Qed.
Lemma lem7069268 {A : Type'} (s : A -> Prop) (f : A -> real) : term66 A s f.
Proof. exact (@lem7069169 A s f True). Qed.
Lemma lem7069269 {A : Type'} (s : A -> Prop) (f : A -> real) : (term27 A s f) = (term67 A s f).
Proof. exact (@lem7069268 A s f (@lem7069267 A s f)). Qed.
Lemma lem7069271 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7069272 {A : Type'} (s : A -> Prop) (f : A -> real) : (term67 A s f) = True.
Proof. exact (@lem7069271 (term21 A s f)). Qed.
Lemma lem7069273 {A : Type'} (s : A -> Prop) (f : A -> real) : (term27 A s f) = True.
Proof. exact (TRANS (@lem7069269 A s f) (@lem7069272 A s f)). Qed.
Lemma lem7069274 {A : Type'} (f : A -> real) : (term29 A f) = (term68 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7069273 A s f)). Qed.
Lemma lem7069275 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7069276 {A : Type'} (f : A -> real) : (term31 A f) = (term69 A).
Proof. exact (MK_COMB (@lem7069275 A) (@lem7069274 A f)). Qed.
Lemma lem7069278 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7069279 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (@lem7069278 (A -> Prop) t). Qed.
Lemma lem7069280 {A : Type'} : (term69 A) = True.
Proof. exact (@lem7069279 A True). Qed.
Lemma lem7069281 {A : Type'} (f : A -> real) : (term31 A f) = True.
Proof. exact (TRANS (@lem7069276 A f) (@lem7069280 A)). Qed.
Lemma lem7069282 {A : Type'} : (term33 A) = (term71 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7069281 A f)). Qed.
Lemma lem7069283 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7069284 {A : Type'} : (term35 A) = (term72 A).
Proof. exact (MK_COMB (@lem7069283 A) (@lem7069282 A)). Qed.
Lemma lem7069286 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7069287 {A : Type'} (t : Prop) : (term73 A t) = t.
Proof. exact (@lem7069286 (A -> real) t). Qed.
Lemma lem7069288 {A : Type'} : (term72 A) = True.
Proof. exact (@lem7069287 A True). Qed.
Lemma lem7069289 {A : Type'} : (term35 A) = True.
Proof. exact (TRANS (@lem7069284 A) (@lem7069288 A)). Qed.
Lemma lem7069290 {A : Type'} : True = (term35 A).
Proof. exact (SYM (@lem7069289 A)). Qed.
Lemma lem7069291 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem7069290 A) (@lem0)). Qed.
Lemma lem7069292 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem7069114 A) (@lem7069291 A)). Qed.
