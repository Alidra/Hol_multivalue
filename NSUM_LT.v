Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_LT_term_abbrevs.
Require Import FINITE_DELETE_spec.
Require Import IN_DELETE_spec.
Require Import LTE_ADD2_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NSUM_CLAUSES_spec.
Require Import NSUM_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem6933026 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term0 A s f g) : term0 A s f g.
Proof. exact (h1). Qed.
Lemma lem6933027 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term1 A s f g) : term1 A s f g.
Proof. exact (h1). Qed.
Lemma lem6933028 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6933029 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term1 A s f g) : term1 A s f g.
Proof. exact (h1). Qed.
Lemma lem6933030 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term2 A s f g) : term2 A s f g.
Proof. exact (h1). Qed.
Lemma lem6933031 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : term3 A s f g.
Proof. exact (h1). Qed.
Lemma lem6933033 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term2 A s f g) : term2 A s f g.
Proof. exact (h1). Qed.
Lemma lem6933034 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term4 A s f g a) : term4 A s f g a.
Proof. exact (h1). Qed.
Lemma lem6933035 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (h1 : term5 A f g a) : term5 A f g a.
Proof. exact (h1). Qed.
Lemma lem6933036 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem6933037 {A : Type'} (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : s = (term6 A s a).
Proof. exact (h1). Qed.
Lemma lem6933038 {A : Type'} (f : A -> nat) (g : A -> nat) : (term7 A f g) = (term7 A f g).
Proof. exact (eq_refl (term7 A f g)). Qed.
Lemma lem6933039 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : (term8 A f g s) = (term9 A f g s a).
Proof. exact (MK_COMB (@lem6933038 A f g) (@lem6933037 A s a h1)). Qed.
Lemma lem6933040 {A : Type'} (f : A -> nat) (s : A -> Prop) (a : A) (g : A -> nat) : (term9 A f g s a) = (term10 A f s a g).
Proof. exact (eq_refl (term9 A f g s a)). Qed.
Lemma lem6933041 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) : (term11 A f g s) = (term11 A f g s).
Proof. exact (eq_refl (term11 A f g s)). Qed.
Lemma lem6933042 {A : Type'} (f : A -> nat) (s : A -> Prop) (a : A) (g : A -> nat) : ((term8 A f g s) = (term9 A f g s a)) = ((term8 A f g s) = (term10 A f s a g)).
Proof. exact (MK_COMB (@lem6933041 A f g s) (@lem6933040 A f s a g)). Qed.
Lemma lem6933043 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term8 A f g s) = (term12 A f s g).
Proof. exact (eq_refl (term8 A f g s)). Qed.
Lemma lem6933044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6933045 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : (term11 A f g s) = (term13 A f s g).
Proof. exact (MK_COMB (@lem6933044) (@lem6933043 A f s g)). Qed.
Lemma lem6933046 {A : Type'} (f : A -> nat) (s : A -> Prop) (a : A) (g : A -> nat) : (term10 A f s a g) = (term10 A f s a g).
Proof. exact (eq_refl (term10 A f s a g)). Qed.
Lemma lem6933047 {A : Type'} (f : A -> nat) (s : A -> Prop) (a : A) (g : A -> nat) : ((term8 A f g s) = (term10 A f s a g)) = ((term12 A f s g) = (term10 A f s a g)).
Proof. exact (MK_COMB (@lem6933045 A f s g) (@lem6933046 A f s a g)). Qed.
Lemma lem6933048 {A : Type'} (f : A -> nat) (s : A -> Prop) (a : A) (g : A -> nat) : ((term8 A f g s) = (term9 A f g s a)) = ((term12 A f s g) = (term10 A f s a g)).
Proof. exact (TRANS (@lem6933042 A f s a g) (@lem6933047 A f s a g)). Qed.
Lemma lem6933049 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : (term12 A f s g) = (term10 A f s a g).
Proof. exact (EQ_MP (@lem6933048 A f s a g) (@lem6933039 A f g s a h1)). Qed.
Lemma lem6933050 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (a : A) (h1 : s = (term6 A s a)) : (term10 A f s a g) = (term12 A f s g).
Proof. exact (SYM (@lem6933049 A f g s a h1)). Qed.
Lemma lem6933056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6933057 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (@lem6933056 A s t). Qed.
Lemma lem6933058 {A : Type'} (s : A -> Prop) (a : A) : (s = (term6 A s a)) = (term15 A s a).
Proof. exact (@lem6933057 A s (term6 A s a)). Qed.
Lemma lem6933067 {A : Type'} (a : A) (s : A -> Prop) : (term16 A a s) = (term16 A a s).
Proof. exact (eq_refl (term16 A a s)). Qed.
Lemma lem6933068 {A : Type'} (s : A -> Prop) (a : A) : (term17 A s a) = (term18 A s a).
Proof. exact (MK_COMB (@lem6933067 A a s) (@lem6933058 A s a)). Qed.
Lemma lem6933071 {A : Type'} (s : A -> Prop) (a : A) : (term18 A s a) = (term17 A s a).
Proof. exact (SYM (@lem6933068 A s a)). Qed.
Lemma lem6933075 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6933076 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6933075 A P x). Qed.
Lemma lem6933077 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem6933076 A s a). Qed.
Lemma lem6933078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6933079 {A : Type'} (s : A -> Prop) (a : A) : (term16 A a s) = (term19 A s a).
Proof. exact (MK_COMB (@lem6933078) (@lem6933077 A s a)). Qed.
Lemma lem6933087 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6933088 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6933087 A P x). Qed.
Lemma lem6933089 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6933088 A s x). Qed.
Lemma lem6933090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6933091 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem6933090) (@lem6933089 A s x)). Qed.
Lemma lem6933093 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term22 A x y s) = (term23 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6933094 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term22 A x y s) = (term23 A y x s).
Proof. exact (@lem6933093 A y x s). Qed.
Lemma lem6933095 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term24 A x s a) = (term25 A x s a).
Proof. exact (@lem6933094 A a x (@DELETE A s a)). Qed.
Lemma lem6933101 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem6933102 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem6933101 A s x y). Qed.
Lemma lem6933103 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term26 A x s a) = (term27 A s x a).
Proof. exact (@lem6933102 A s x a). Qed.
Lemma lem6933107 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6933108 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6933107 A P x). Qed.
Lemma lem6933109 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6933108 A s x). Qed.
Lemma lem6933110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6933111 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term29 A s x).
Proof. exact (MK_COMB (@lem6933110) (@lem6933109 A s x)). Qed.
Lemma lem6933114 {A : Type'} (x : A) (a : A) : (term30 A x a) = (term30 A x a).
Proof. exact (eq_refl (term30 A x a)). Qed.
Lemma lem6933115 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term27 A s x a) = (term31 A s x a).
Proof. exact (MK_COMB (@lem6933111 A s x) (@lem6933114 A x a)). Qed.
Lemma lem6933118 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term26 A x s a) = (term31 A s x a).
Proof. exact (TRANS (@lem6933103 A s x a) (@lem6933115 A s x a)). Qed.
Lemma lem6933119 {A : Type'} (x : A) (a : A) : (term32 A x a) = (term32 A x a).
Proof. exact (eq_refl (term32 A x a)). Qed.
Lemma lem6933120 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term25 A x s a) = (term33 A s x a).
Proof. exact (MK_COMB (@lem6933119 A x a) (@lem6933118 A s x a)). Qed.
Lemma lem6933123 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term24 A x s a) = (term33 A s x a).
Proof. exact (TRANS (@lem6933095 A x s a) (@lem6933120 A s x a)). Qed.
Lemma lem6933124 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((@IN A x s) = (term24 A x s a)) = ((s x) = (term33 A s x a)).
Proof. exact (MK_COMB (@lem6933091 A s x) (@lem6933123 A s x a)). Qed.
Lemma lem6933127 {A : Type'} (s : A -> Prop) (a : A) : (term34 A s a) = (term35 A s a).
Proof. exact (fun_ext (fun x : A => @lem6933124 A s x a)). Qed.
Lemma lem6933128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6933129 {A : Type'} (s : A -> Prop) (a : A) : (term15 A s a) = (term36 A s a).
Proof. exact (MK_COMB (@lem6933128 A) (@lem6933127 A s a)). Qed.
Lemma lem6933134 {A : Type'} (s : A -> Prop) (a : A) : (term18 A s a) = (term37 A s a).
Proof. exact (MK_COMB (@lem6933079 A s a) (@lem6933129 A s a)). Qed.
Lemma lem6933137 {A : Type'} (s : A -> Prop) (a : A) : (term37 A s a) = (term18 A s a).
Proof. exact (SYM (@lem6933134 A s a)). Qed.
Lemma lem6933139 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6933140 {A : Type'} (s : A -> Prop) (a : A) : (term37 A s a) = (term39 A s a).
Proof. exact (@lem6933139 (term37 A s a)). Qed.
Lemma lem6933141 {A : Type'} (s : A -> Prop) (a : A) : (term39 A s a) = (term37 A s a).
Proof. exact (SYM (@lem6933140 A s a)). Qed.
Lemma lem6933142 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : term40 A s a.
Proof. exact (h1). Qed.
Lemma lem6933145 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) : term39 A s a.
Proof. exact (h1). Qed.
Lemma lem6933146 {A : Type'} (s : A -> Prop) (a : A) : term41 A s a.
Proof. exact (fun h0 : term39 A s a => @lem6933145 A s a h0). Qed.
Lemma lem6933147 {A : Type'} (s : A -> Prop) (a : A) (h1 : term41 A s a) : term41 A s a.
Proof. exact (h1). Qed.
Lemma lem6933148 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) : term39 A s a.
Proof. exact (h1). Qed.
Lemma lem6933149 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) (h2 : term41 A s a) : term39 A s a.
Proof. exact (@lem6933147 A s a h2 (@lem6933148 A s a h1)). Qed.
Lemma lem6933150 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) : term42 A s a.
Proof. exact (fun h0 : term41 A s a => @lem6933149 A s a h1 h0). Qed.
Lemma lem6933151 {A : Type'} (s : A -> Prop) (a : A) (h1 : term41 A s a) : term41 A s a.
Proof. exact (h1). Qed.
Lemma lem6933152 {A : Type'} (s : A -> Prop) (a : A) (h1 : term39 A s a) (h2 : term41 A s a) : term39 A s a.
Proof. exact (@lem6933150 A s a h1 (@lem6933151 A s a h2)). Qed.
Lemma lem6933153 {A : Type'} (s : A -> Prop) (a : A) (h1 : term41 A s a) : term41 A s a.
Proof. exact (fun h0 : term39 A s a => @lem6933152 A s a h0 h1). Qed.
Lemma lem6933154 {A : Type'} (s : A -> Prop) (a : A) : term43 A s a.
Proof. exact (fun h0 : term41 A s a => @lem6933153 A s a h0). Qed.
Lemma lem6933157 {A : Type'} (s : A -> Prop) (a : A) : term41 A s a.
Proof. exact (@lem6933154 A s a (@lem6933146 A s a)). Qed.
Lemma lem6933158 {A : Type'} (s : A -> Prop) (a : A) : term41 A s a.
Proof. exact (@lem6933157 A s a). Qed.
Lemma lem6933168 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6933169 {A : Type'} (s : A -> Prop) (a : A) : (term39 A s a) = (term44 A s a).
Proof. exact (@lem6933168 (term40 A s a)). Qed.
Lemma lem6933171 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6933172 {A : Type'} (s : A -> Prop) (a : A) : (term44 A s a) = (term37 A s a).
Proof. exact (@lem6933171 (term37 A s a)). Qed.
Lemma lem6933175 {A : Type'} (s : A -> Prop) (a : A) : (term39 A s a) = (term37 A s a).
Proof. exact (TRANS (@lem6933169 A s a) (@lem6933172 A s a)). Qed.
Lemma lem6933184 {A : Type'} (a : A) : (term46 A a) = (term47 A a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6933175 A s a)). Qed.
Lemma lem6933185 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6933186 {A : Type'} (a : A) : (term48 A a) = (term49 A a).
Proof. exact (MK_COMB (@lem6933185 A) (@lem6933184 A a)). Qed.
Lemma lem6933191 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (fun_ext (fun a : A => @lem6933186 A a)). Qed.
Lemma lem6933192 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6933201 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (MK_COMB (@lem6933192 A) (@lem6933191 A)). Qed.
Lemma lem6933216 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((s x) = (term33 A s x a)) = ((s x) = (term33 A s x a)).
Proof. exact (eq_refl ((s x) = (term33 A s x a))). Qed.
Lemma lem6933217 {A : Type'} (s : A -> Prop) (a : A) : (term35 A s a) = (term35 A s a).
Proof. exact (fun_ext (fun x : A => @lem6933216 A s x a)). Qed.
Lemma lem6933218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6933219 {A : Type'} (s : A -> Prop) (a : A) : (term36 A s a) = (term36 A s a).
Proof. exact (MK_COMB (@lem6933218 A) (@lem6933217 A s a)). Qed.
Lemma lem6933222 {A : Type'} (s : A -> Prop) (a : A) : (term19 A s a) = (term19 A s a).
Proof. exact (eq_refl (term19 A s a)). Qed.
Lemma lem6933223 {A : Type'} (s : A -> Prop) (a : A) : (term37 A s a) = (term37 A s a).
Proof. exact (MK_COMB (@lem6933222 A s a) (@lem6933219 A s a)). Qed.
Lemma lem6933224 {A : Type'} (a : A) : (term47 A a) = (term47 A a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6933223 A s a)). Qed.
Lemma lem6933225 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6933226 {A : Type'} (a : A) : (term49 A a) = (term49 A a).
Proof. exact (MK_COMB (@lem6933225 A) (@lem6933224 A a)). Qed.
Lemma lem6933227 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun a : A => @lem6933226 A a)). Qed.
Lemma lem6933228 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6933229 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (MK_COMB (@lem6933228 A) (@lem6933227 A)). Qed.
Lemma lem6933256 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (TRANS (@lem6933201 A) (@lem6933229 A)). Qed.
Lemma lem6933257 {A : Type'} : (term53 A) = (term52 A).
Proof. exact (SYM (@lem6933256 A)). Qed.
Lemma lem6933260 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6933261 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((s x) = (term33 A s x a)) = (term54 A s x a).
Proof. exact (@lem6933260 ((s x) = (term33 A s x a))). Qed.
Lemma lem6933262 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term54 A s x a) = ((s x) = (term33 A s x a)).
Proof. exact (SYM (@lem6933261 A s x a)). Qed.
Lemma lem6933263 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term55 A s x a) : term55 A s x a.
Proof. exact (h1). Qed.
Lemma lem6933269 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem6933279 {A : Type'} (x : A) (a : A) : (term56 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem6933281 {A : Type'} (s : A -> Prop) (x : A) : (term57 A s x) = (term57 A s x).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem6933282 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term58 A s x a) = (term59 A s x a).
Proof. exact (MK_COMB (@lem6933281 A s x) (@lem6933279 A x a)). Qed.
Lemma lem6933283 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term60 A s x a) = (term58 A s x a).
Proof. exact (@lem17045 (s x) (term30 A x a)). Qed.
Lemma lem6933284 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term60 A s x a) = (term59 A s x a).
Proof. exact (TRANS (@lem6933283 A s x a) (@lem6933282 A s x a)). Qed.
Lemma lem6933289 {A : Type'} (x : A) (a : A) : (term61 A x a) = (term61 A x a).
Proof. exact (eq_refl (term61 A x a)). Qed.
Lemma lem6933290 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term62 A s x a) = (term63 A s x a).
Proof. exact (MK_COMB (@lem6933289 A x a) (@lem6933284 A s x a)). Qed.
Lemma lem6933291 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term64 A s x a) = (term62 A s x a).
Proof. exact (@lem17160 (x = a) (term31 A s x a)). Qed.
Lemma lem6933292 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term64 A s x a) = (term63 A s x a).
Proof. exact (TRANS (@lem6933291 A s x a) (@lem6933290 A s x a)). Qed.
Lemma lem6933298 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term65 A s x a) = (term65 A s x a).
Proof. exact (eq_refl (term65 A s x a)). Qed.
Lemma lem6933300 {A : Type'} (s : A -> Prop) (x : A) : (term29 A s x) = (term29 A s x).
Proof. exact (eq_refl (term29 A s x)). Qed.
Lemma lem6933301 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term66 A s x a) = (term67 A s x a).
Proof. exact (MK_COMB (@lem6933300 A s x) (@lem6933292 A s x a)). Qed.
Lemma lem6933302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6933303 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term68 A s x a) = (term69 A s x a).
Proof. exact (MK_COMB (@lem6933302) (@lem6933301 A s x a)). Qed.
Lemma lem6933304 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term70 A s x a) = (term71 A s x a).
Proof. exact (MK_COMB (@lem6933303 A s x a) (@lem6933298 A s x a)). Qed.
Lemma lem6933305 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term55 A s x a) = (term70 A s x a).
Proof. exact (@lem17646 (s x) (term33 A s x a)). Qed.
Lemma lem6933310 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term55 A s x a) = (term71 A s x a).
Proof. exact (TRANS (@lem6933305 A s x a) (@lem6933304 A s x a)). Qed.
Lemma lem6933315 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem6933377 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term55 A s x a) : term71 A s x a.
Proof. exact (EQ_MP (@lem6933310 A s x a) (@lem6933263 A s x a h1)). Qed.
Lemma lem6933378 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term67 A s x a.
Proof. exact (h1). Qed.
Lemma lem6933379 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term65 A s x a.
Proof. exact (h1). Qed.
Lemma lem6933380 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term63 A s x a.
Proof. exact (proj2 (@lem6933378 A s x a h1)). Qed.
Lemma lem6933382 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term59 A s x a.
Proof. exact (proj2 (@lem6933380 A s x a h1)). Qed.
Lemma lem6933386 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term33 A s x a.
Proof. exact (proj2 (@lem6933379 A s x a h1)). Qed.
Lemma lem6933389 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : term31 A s x a.
Proof. exact (h1). Qed.
Lemma lem6933407 {A : Type'} (s : A -> Prop) (x : A) (h1 : term72 A s x) : term72 A s x.
Proof. exact (h1). Qed.
Lemma lem6933423 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem6933427 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem6933435 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem6933459 {A : Type'} (s : A -> Prop) (x : A) (h1 : term72 A s x) : term72 A s x.
Proof. exact (h1). Qed.
Lemma lem6933465 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term30 A x a.
Proof. exact (proj1 (@lem6933380 A s x a h1)). Qed.
Lemma lem6933467 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem6933469 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem6933471 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term72 A s x.
Proof. exact (proj1 (@lem6933379 A s x a h1)). Qed.
Lemma lem6933473 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem6933477 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term72 A s x.
Proof. exact (proj1 (@lem6933379 A s x a h1)). Qed.
Lemma lem6933523 {A : Type'} (a : A) : (term73 A a) = (term73 A a).
Proof. exact (eq_refl (term73 A a)). Qed.
Lemma lem6933524 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term74 A a x) = (term75 A a).
Proof. exact (MK_COMB (@lem6933523 A a) (@lem6933467 A x a h1)). Qed.
Lemma lem6933525 {A : Type'} (a : A) : (term75 A a) = (term76 A a).
Proof. exact (eq_refl (term75 A a)). Qed.
Lemma lem6933526 {A : Type'} (a : A) (x : A) : (term77 A a x) = (term77 A a x).
Proof. exact (eq_refl (term77 A a x)). Qed.
Lemma lem6933527 {A : Type'} (x : A) (a : A) : ((term74 A a x) = (term75 A a)) = ((term74 A a x) = (term76 A a)).
Proof. exact (MK_COMB (@lem6933526 A a x) (@lem6933525 A a)). Qed.
Lemma lem6933528 {A : Type'} (x : A) (a : A) : (term74 A a x) = (term30 A x a).
Proof. exact (eq_refl (term74 A a x)). Qed.
Lemma lem6933529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6933530 {A : Type'} (x : A) (a : A) : (term77 A a x) = (term78 A x a).
Proof. exact (MK_COMB (@lem6933529) (@lem6933528 A x a)). Qed.
Lemma lem6933531 {A : Type'} (a : A) : (term76 A a) = (term76 A a).
Proof. exact (eq_refl (term76 A a)). Qed.
Lemma lem6933532 {A : Type'} (x : A) (a : A) : ((term74 A a x) = (term76 A a)) = ((term30 A x a) = (term76 A a)).
Proof. exact (MK_COMB (@lem6933530 A x a) (@lem6933531 A a)). Qed.
Lemma lem6933533 {A : Type'} (x : A) (a : A) : ((term74 A a x) = (term75 A a)) = ((term30 A x a) = (term76 A a)).
Proof. exact (TRANS (@lem6933527 A x a) (@lem6933532 A x a)). Qed.
Lemma lem6933534 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term30 A x a) = (term76 A a).
Proof. exact (EQ_MP (@lem6933533 A x a) (@lem6933524 A x a h1)). Qed.
Lemma lem6933535 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : term76 A a.
Proof. exact (EQ_MP (@lem6933534 A x a h2) (@lem6933465 A s x a h1)). Qed.
Lemma lem6933563 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem6933564 {A : Type'} (s : A -> Prop) : (term79 A s) = (term79 A s).
Proof. exact (eq_refl (term79 A s)). Qed.
Lemma lem6933565 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term80 A s x) = (term80 A s a).
Proof. exact (MK_COMB (@lem6933564 A s) (@lem6933473 A x a h1)). Qed.
Lemma lem6933566 {A : Type'} (s : A -> Prop) (a : A) : (term80 A s a) = (term72 A s a).
Proof. exact (eq_refl (term80 A s a)). Qed.
Lemma lem6933567 {A : Type'} (s : A -> Prop) (x : A) : (term81 A s x) = (term81 A s x).
Proof. exact (eq_refl (term81 A s x)). Qed.
Lemma lem6933568 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term80 A s x) = (term80 A s a)) = ((term80 A s x) = (term72 A s a)).
Proof. exact (MK_COMB (@lem6933567 A s x) (@lem6933566 A s a)). Qed.
Lemma lem6933569 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (term72 A s x).
Proof. exact (eq_refl (term80 A s x)). Qed.
Lemma lem6933570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6933571 {A : Type'} (s : A -> Prop) (x : A) : (term81 A s x) = (term82 A s x).
Proof. exact (MK_COMB (@lem6933570) (@lem6933569 A s x)). Qed.
Lemma lem6933572 {A : Type'} (s : A -> Prop) (a : A) : (term72 A s a) = (term72 A s a).
Proof. exact (eq_refl (term72 A s a)). Qed.
Lemma lem6933573 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term80 A s x) = (term72 A s a)) = ((term72 A s x) = (term72 A s a)).
Proof. exact (MK_COMB (@lem6933571 A s x) (@lem6933572 A s a)). Qed.
Lemma lem6933574 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term80 A s x) = (term80 A s a)) = ((term72 A s x) = (term72 A s a)).
Proof. exact (TRANS (@lem6933568 A x s a) (@lem6933573 A x s a)). Qed.
Lemma lem6933575 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term72 A s x) = (term72 A s a).
Proof. exact (EQ_MP (@lem6933574 A x s a) (@lem6933565 A s x a h1)). Qed.
Lemma lem6933576 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : x = a) : term72 A s a.
Proof. exact (EQ_MP (@lem6933575 A s x a h2) (@lem6933471 A s x a h1)). Qed.
Lemma lem6933592 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : s x.
Proof. exact (proj1 (@lem6933378 A s x a h1)). Qed.
Lemma lem6933593 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : term83 A s x.
Proof. exact (fun h0 : term72 A s x => @lem6933592 A s x a h1). Qed.
Lemma lem6933595 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933596 {A : Type'} (s : A -> Prop) (x : A) : (term83 A s x) = (s x).
Proof. exact (@lem6933595 (s x)). Qed.
Lemma lem6933597 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : s x.
Proof. exact (EQ_MP (@lem6933596 A s x) (@lem6933593 A s x a h1)). Qed.
Lemma lem6933600 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6933602 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term85 A s x).
Proof. exact (@lem6933600 (s x)). Qed.
Lemma lem6933605 {A : Type'} (s : A -> Prop) (x : A) (h1 : term72 A s x) : term85 A s x.
Proof. exact (EQ_MP (@lem6933602 A s x) (@lem6933459 A s x h1)). Qed.
Lemma lem6933608 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (@lem6933605 A s x h1 (@lem6933597 A s x a h2)). Qed.
Lemma lem6933609 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : term86.
Proof. exact (fun h0 : ~ False => @lem6933608 A s x a h1 h2). Qed.
Lemma lem6933611 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933612 : term86 = False.
Proof. exact (@lem6933611 False). Qed.
Lemma lem6933613 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem6933612) (@lem6933609 A s x a h1 h2)). Qed.
Lemma lem6933629 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem6933630 {A : Type'} (x : A) : x = x.
Proof. exact (@lem6933629 A x). Qed.
Lemma lem6933631 {A : Type'} (a : A) : a = a.
Proof. exact (@lem6933630 A a). Qed.
Lemma lem6933632 {A : Type'} (a : A) : term87 A a.
Proof. exact (fun h0 : term76 A a => @lem6933631 A a). Qed.
Lemma lem6933634 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933635 {A : Type'} (a : A) : (term87 A a) = (a = a).
Proof. exact (@lem6933634 (a = a)). Qed.
Lemma lem6933636 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem6933635 A a) (@lem6933632 A a)). Qed.
Lemma lem6933639 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6933641 {A : Type'} (a : A) : (term76 A a) = (term88 A a).
Proof. exact (@lem6933639 (a = a)). Qed.
Lemma lem6933644 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : term88 A a.
Proof. exact (EQ_MP (@lem6933641 A a) (@lem6933535 A s x a h1 h2)). Qed.
Lemma lem6933647 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (@lem6933644 A s x a h1 h2 (@lem6933636 A a)). Qed.
Lemma lem6933648 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : term86.
Proof. exact (fun h0 : ~ False => @lem6933647 A s x a h1 h2). Qed.
Lemma lem6933650 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933651 : term86 = False.
Proof. exact (@lem6933650 False). Qed.
Lemma lem6933654 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem6933655 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term83 A s a.
Proof. exact (fun h0 : term72 A s a => @lem6933654 A s a h1). Qed.
Lemma lem6933657 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933658 {A : Type'} (s : A -> Prop) (a : A) : (term83 A s a) = (s a).
Proof. exact (@lem6933657 (s a)). Qed.
Lemma lem6933659 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (EQ_MP (@lem6933658 A s a) (@lem6933655 A s a h1)). Qed.
Lemma lem6933662 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6933664 {A : Type'} (s : A -> Prop) (a : A) : (term72 A s a) = (term85 A s a).
Proof. exact (@lem6933662 (s a)). Qed.
Lemma lem6933667 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : x = a) : term85 A s a.
Proof. exact (EQ_MP (@lem6933664 A s a) (@lem6933576 A s x a h1 h2)). Qed.
Lemma lem6933670 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (@lem6933667 A s x a h2 h3 (@lem6933659 A s a h1)). Qed.
Lemma lem6933671 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : term86.
Proof. exact (fun h0 : ~ False => @lem6933670 A s x a h1 h2 h3). Qed.
Lemma lem6933673 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933674 : term86 = False.
Proof. exact (@lem6933673 False). Qed.
Lemma lem6933675 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933674) (@lem6933671 A s x a h1 h2 h3)). Qed.
Lemma lem6933691 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : s x.
Proof. exact (proj1 (@lem6933389 A s x a h1)). Qed.
Lemma lem6933692 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : term83 A s x.
Proof. exact (fun h0 : term72 A s x => @lem6933691 A s x a h1). Qed.
Lemma lem6933694 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933695 {A : Type'} (s : A -> Prop) (x : A) : (term83 A s x) = (s x).
Proof. exact (@lem6933694 (s x)). Qed.
Lemma lem6933696 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term31 A s x a) : s x.
Proof. exact (EQ_MP (@lem6933695 A s x) (@lem6933692 A s x a h1)). Qed.
Lemma lem6933699 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6933701 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term85 A s x).
Proof. exact (@lem6933699 (s x)). Qed.
Lemma lem6933704 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) : term85 A s x.
Proof. exact (EQ_MP (@lem6933701 A s x) (@lem6933477 A s x a h1)). Qed.
Lemma lem6933707 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : term31 A s x a) : False.
Proof. exact (@lem6933704 A s x a h1 (@lem6933696 A s x a h2)). Qed.
Lemma lem6933708 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : term31 A s x a) : term86.
Proof. exact (fun h0 : ~ False => @lem6933707 A s x a h1 h2). Qed.
Lemma lem6933710 (p : Prop) : (term84 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6933711 : term86 = False.
Proof. exact (@lem6933710 False). Qed.
Lemma lem6933712 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term65 A s x a) (h2 : term31 A s x a) : False.
Proof. exact (EQ_MP (@lem6933711) (@lem6933708 A s x a h1 h2)). Qed.
Lemma lem6933713 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem6933675 A s x a h1 h2 h3) (fun h4 : False => @lem6933563 A s a h1)). Qed.
Lemma lem6933715 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933713 A s x a h1 h2 h3) (@lem6933563 A s a h1)). Qed.
Lemma lem6933716 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem6933651) (@lem6933648 A s x a h1 h2)). Qed.
Lemma lem6933717 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem6933715 A s x a h1 h2 h3) (fun h4 : False => @lem6933473 A x a h3)). Qed.
Lemma lem6933718 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933717 A s x a h1 h2 h3) (@lem6933473 A x a h3)). Qed.
Lemma lem6933719 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem6933718 A s x a h1 h2 h3) (fun h4 : False => @lem6933469 A s a h1)). Qed.
Lemma lem6933720 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933719 A s x a h1 h2 h3) (@lem6933469 A s a h1)). Qed.
Lemma lem6933721 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem6933716 A s x a h1 h2) (fun h3 : False => @lem6933467 A x a h2)). Qed.
Lemma lem6933722 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem6933721 A s x a h1 h2) (@lem6933467 A x a h2)). Qed.
Lemma lem6933723 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : (term72 A s x) = False.
Proof. exact (prop_ext (fun h3 : term72 A s x => @lem6933613 A s x a h1 h2) (fun h3 : False => @lem6933459 A s x h1)). Qed.
Lemma lem6933724 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem6933723 A s x a h1 h2) (@lem6933459 A s x h1)). Qed.
Lemma lem6933725 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem6933720 A s x a h1 h2 h3) (fun h4 : False => @lem6933435 A x a h3)). Qed.
Lemma lem6933726 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933725 A s x a h1 h2 h3) (@lem6933435 A x a h3)). Qed.
Lemma lem6933727 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem6933726 A s x a h1 h2 h3) (fun h4 : False => @lem6933427 A s a h1)). Qed.
Lemma lem6933728 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933727 A s x a h1 h2 h3) (@lem6933427 A s a h1)). Qed.
Lemma lem6933729 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem6933722 A s x a h1 h2) (fun h3 : False => @lem6933423 A x a h2)). Qed.
Lemma lem6933730 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem6933729 A s x a h1 h2) (@lem6933423 A x a h2)). Qed.
Lemma lem6933731 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : (term72 A s x) = False.
Proof. exact (prop_ext (fun h3 : term72 A s x => @lem6933724 A s x a h1 h2) (fun h3 : False => @lem6933407 A s x h1)). Qed.
Lemma lem6933732 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem6933731 A s x a h1 h2) (@lem6933407 A s x h1)). Qed.
Lemma lem6933733 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem6933728 A s x a h1 h2 h3) (fun h4 : False => @lem6933435 A x a h3)). Qed.
Lemma lem6933734 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933733 A s x a h1 h2 h3) (@lem6933435 A x a h3)). Qed.
Lemma lem6933735 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem6933734 A s x a h1 h2 h3) (fun h4 : False => @lem6933427 A s a h1)). Qed.
Lemma lem6933736 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem6933735 A s x a h1 h2 h3) (@lem6933427 A s a h1)). Qed.
Lemma lem6933737 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem6933730 A s x a h1 h2) (fun h3 : False => @lem6933423 A x a h2)). Qed.
Lemma lem6933738 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem6933737 A s x a h1 h2) (@lem6933423 A x a h2)). Qed.
Lemma lem6933739 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : (term72 A s x) = False.
Proof. exact (prop_ext (fun h3 : term72 A s x => @lem6933732 A s x a h1 h2) (fun h3 : False => @lem6933407 A s x h1)). Qed.
Lemma lem6933740 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term72 A s x) (h2 : term67 A s x a) : False.
Proof. exact (EQ_MP (@lem6933739 A s x a h1 h2) (@lem6933407 A s x h1)). Qed.
Lemma lem6933741 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term65 A s x a) : False.
Proof. exact (or_elim (@lem6933386 A s x a h2) (fun h0 : x = a => @lem6933736 A s x a h1 h2 h0) (fun h0 : term31 A s x a => @lem6933712 A s x a h2 h0)). Qed.
Lemma lem6933742 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term67 A s x a) : False.
Proof. exact (or_elim (@lem6933382 A s x a h1) (fun h0 : term72 A s x => @lem6933740 A s x a h0 h1) (fun h0 : x = a => @lem6933738 A s x a h1 h0)). Qed.
Lemma lem6933743 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (or_elim (@lem6933377 A s x a h1) (fun h0 : term67 A s x a => @lem6933742 A s x a h0) (fun h0 : term65 A s x a => @lem6933741 A s x a h2 h0)). Qed.
Lemma lem6933744 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem6933743 A x s a h1 h2) (fun h3 : False => @lem6933315 A s a h2)). Qed.
Lemma lem6933745 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem6933744 A x s a h1 h2) (@lem6933315 A s a h2)). Qed.
Lemma lem6933746 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem6933745 A x s a h1 h2) (fun h3 : False => @lem6933269 A s a h2)). Qed.
Lemma lem6933747 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem6933746 A x s a h1 h2) (@lem6933269 A s a h2)). Qed.
Lemma lem6933748 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : (term55 A s x a) = False.
Proof. exact (prop_ext (fun h3 : term55 A s x a => @lem6933747 A x s a h1 h2) (fun h3 : False => @lem6933263 A s x a h1)). Qed.
Lemma lem6933749 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term55 A s x a) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem6933748 A x s a h1 h2) (@lem6933263 A s x a h1)). Qed.
Lemma lem6933750 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : term54 A s x a.
Proof. exact (fun h0 : term55 A s x a => @lem6933749 A x s a h0 h1). Qed.
Lemma lem6933751 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : (s x) = (term33 A s x a).
Proof. exact (EQ_MP (@lem6933262 A s x a) (@lem6933750 A x s a h1)). Qed.
Lemma lem6933756 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term36 A s a.
Proof. exact (fun x : A => @lem6933751 A x s a h1). Qed.
Lemma lem6933757 {A : Type'} (s : A -> Prop) (a : A) : term37 A s a.
Proof. exact (fun h0 : s a => @lem6933756 A s a h0). Qed.
Lemma lem6933762 {A : Type'} (a : A) : term49 A a.
Proof. exact (fun s : A -> Prop => @lem6933757 A s a). Qed.
Lemma lem6933767 {A : Type'} : term53 A.
Proof. exact (fun a : A => @lem6933762 A a). Qed.
Lemma lem6933768 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem6933257 A) (@lem6933767 A)). Qed.
Lemma lem6933769 {A : Type'} (a : A) : term89 A a.
Proof. exact (@lem6933768 A a). Qed.
Lemma lem6933770 {A : Type'} (a : A) : (term89 A a) = (term48 A a).
Proof. exact (eq_refl (term89 A a)). Qed.
Lemma lem6933771 {A : Type'} (a : A) : term48 A a.
Proof. exact (EQ_MP (@lem6933770 A a) (@lem6933769 A a)). Qed.
Lemma lem6933772 {A : Type'} (a : A) (s : A -> Prop) : term90 A a s.
Proof. exact (@lem6933771 A a s). Qed.
Lemma lem6933773 {A : Type'} (s : A -> Prop) (a : A) : (term90 A a s) = (term39 A s a).
Proof. exact (eq_refl (term90 A a s)). Qed.
Lemma lem6933774 {A : Type'} (s : A -> Prop) (a : A) : term39 A s a.
Proof. exact (EQ_MP (@lem6933773 A s a) (@lem6933772 A a s)). Qed.
Lemma lem6933776 {A : Type'} (s : A -> Prop) (a : A) : term39 A s a.
Proof. exact (@lem6933158 A s a (@lem6933774 A s a)). Qed.
Lemma lem6933777 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : False.
Proof. exact (@lem6933776 A s a (@lem6933142 A s a h1)). Qed.
Lemma lem6933778 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : (term40 A s a) = False.
Proof. exact (prop_ext (fun h2 : term40 A s a => @lem6933777 A s a h1) (fun h2 : False => @lem6933142 A s a h1)). Qed.
Lemma lem6933779 {A : Type'} (s : A -> Prop) (a : A) (h1 : term40 A s a) : False.
Proof. exact (EQ_MP (@lem6933778 A s a h1) (@lem6933142 A s a h1)). Qed.
Lemma lem6933780 {A : Type'} (s : A -> Prop) (a : A) : term39 A s a.
Proof. exact (fun h0 : term40 A s a => @lem6933779 A s a h0). Qed.
Lemma lem6933781 {A : Type'} (s : A -> Prop) (a : A) : term37 A s a.
Proof. exact (EQ_MP (@lem6933141 A s a) (@lem6933780 A s a)). Qed.
Lemma lem6933782 {A : Type'} (s : A -> Prop) (a : A) : term18 A s a.
Proof. exact (EQ_MP (@lem6933137 A s a) (@lem6933781 A s a)). Qed.
Lemma lem6933783 {A : Type'} (s : A -> Prop) (a : A) : term17 A s a.
Proof. exact (EQ_MP (@lem6933071 A s a) (@lem6933782 A s a)). Qed.
Lemma lem6933784 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : s = (term6 A s a).
Proof. exact (@lem6933783 A s a (@lem6933036 A a s h1)). Qed.
Lemma lem6933785 {A : Type'} (s : A -> Prop) : term91 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem6933786 {A : Type'} (s : A -> Prop) : (term91 A s) = (term92 A s).
Proof. exact (eq_refl (term91 A s)). Qed.
Lemma lem6933787 {A : Type'} (s : A -> Prop) : term92 A s.
Proof. exact (EQ_MP (@lem6933786 A s) (@lem6933785 A s)). Qed.
Lemma lem6933788 {A : Type'} (s : A -> Prop) (x : A) : term93 A s x.
Proof. exact (@lem6933787 A s x). Qed.
Lemma lem6933789 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term94 A s x).
Proof. exact (eq_refl (term93 A s x)). Qed.
Lemma lem6933790 {A : Type'} (s : A -> Prop) (x : A) : term94 A s x.
Proof. exact (EQ_MP (@lem6933789 A s x) (@lem6933788 A s x)). Qed.
Lemma lem6933791 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term95 A s x y.
Proof. exact (@lem6933790 A s x y). Qed.
Lemma lem6933792 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term95 A s x y) = ((term26 A x s y) = (term27 A s x y)).
Proof. exact (eq_refl (term95 A s x y)). Qed.
Lemma lem6933794 {A : Type'} (s : A -> Prop) : term96 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem6933795 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (eq_refl (term96 A s)). Qed.
Lemma lem6933796 {A : Type'} (s : A -> Prop) : term97 A s.
Proof. exact (EQ_MP (@lem6933795 A s) (@lem6933794 A s)). Qed.
Lemma lem6933797 {A : Type'} (s : A -> Prop) (x : A) : term98 A s x.
Proof. exact (@lem6933796 A s x). Qed.
Lemma lem6933798 {A : Type'} (x : A) (s : A -> Prop) : (term98 A s x) = ((term99 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem6933800 {_126525 : Type'} : term100 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem6933801 {_126525 : Type'} (x : _126525) : term101 _126525 x.
Proof. exact (@lem6933800 _126525 x). Qed.
Lemma lem6933802 {_126525 : Type'} (x : _126525) : (term101 _126525 x) = (term102 _126525 x).
Proof. exact (eq_refl (term101 _126525 x)). Qed.
Lemma lem6933803 {_126525 : Type'} (x : _126525) : term102 _126525 x.
Proof. exact (EQ_MP (@lem6933802 _126525 x) (@lem6933801 _126525 x)). Qed.
Lemma lem6933804 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term103 _126525 x f.
Proof. exact (@lem6933803 _126525 x f). Qed.
Lemma lem6933805 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term103 _126525 x f) = (term104 _126525 x f).
Proof. exact (eq_refl (term103 _126525 x f)). Qed.
Lemma lem6933806 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term104 _126525 x f.
Proof. exact (EQ_MP (@lem6933805 _126525 x f) (@lem6933804 _126525 x f)). Qed.
Lemma lem6933807 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term105 _126525 x f s.
Proof. exact (@lem6933806 _126525 x f s). Qed.
Lemma lem6933808 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term105 _126525 x f s) = (term106 _126525 x s f).
Proof. exact (eq_refl (term105 _126525 x f s)). Qed.
Lemma lem6933809 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term106 _126525 x s f.
Proof. exact (EQ_MP (@lem6933808 _126525 x s f) (@lem6933807 _126525 x f s)). Qed.
Lemma lem6933810 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem6933811 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term107 _126525 x s f) = (term108 _126525 x s f).
Proof. exact (@lem6933809 _126525 x s f (@lem6933810 _126525 s h1)). Qed.
Lemma lem6933821 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6933835 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = ((@IN A a s) = True).
Proof. exact (@lem7 (@IN A a s)). Qed.
Lemma lem6933840 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term106 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6933811 _126525 x f s h0). Qed.
Lemma lem6933841 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term106 A x s f.
Proof. exact (@lem6933840 A x s f). Qed.
Lemma lem6933842 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) : term109 A s a f.
Proof. exact (@lem6933841 A a (@DELETE A s a) f). Qed.
Lemma lem6933844 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem6933798 A x s) (@lem6933797 A s x)). Qed.
Lemma lem6933845 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (@lem6933844 A x s). Qed.
Lemma lem6933846 {A : Type'} (a : A) (s : A -> Prop) : (term99 A s a) = (@FINITE A s).
Proof. exact (@lem6933845 A a s). Qed.
Lemma lem6933848 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6933821 A s) (@lem6933028 A s h1)). Qed.
Lemma lem6933849 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term99 A s a) = True.
Proof. exact (TRANS (@lem6933846 A a s) (@lem6933848 A s h1)). Qed.
Lemma lem6933850 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : True = (term99 A s a).
Proof. exact (SYM (@lem6933849 A a s h1)). Qed.
Lemma lem6933851 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : term99 A s a.
Proof. exact (EQ_MP (@lem6933850 A a s h1) (@lem0)). Qed.
Lemma lem6933852 {A : Type'} (a : A) (f : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term110 A s a f) = (term111 A s a f).
Proof. exact (@lem6933842 A s a f (@lem6933851 A a s h1)). Qed.
Lemma lem6933854 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term112 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6933855 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term113 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6933854 _2963 g t e g' t' e'). Qed.
Lemma lem6933856 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term114 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6933855 _2963 g t e g' t'). Qed.
Lemma lem6933857 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term115 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6933856 _2963 g t e g'). Qed.
Lemma lem6933858 (g : Prop) (t : nat) (e : nat) : term116 g t e.
Proof. exact (@lem6933857 nat g t e). Qed.
Lemma lem6933859 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) : term117 A s a f.
Proof. exact (@lem6933858 (term118 A s a) (term119 A s a f) (term120 A s a f)). Qed.
Lemma lem6933860 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) : term121 A s a f g'.
Proof. exact (@lem6933859 A s a f g'). Qed.
Lemma lem6933861 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) : (term121 A s a f g') = (term122 A s a f g').
Proof. exact (eq_refl (term121 A s a f g')). Qed.
Lemma lem6933862 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) : term122 A s a f g'.
Proof. exact (EQ_MP (@lem6933861 A s a f g') (@lem6933860 A s a f g')). Qed.
Lemma lem6933863 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) (t' : nat) : term123 A s a f g' t'.
Proof. exact (@lem6933862 A s a f g' t'). Qed.
Lemma lem6933864 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) (t' : nat) : (term123 A s a f g' t') = (term124 A s a f g' t').
Proof. exact (eq_refl (term123 A s a f g' t')). Qed.
Lemma lem6933865 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) (t' : nat) : term124 A s a f g' t'.
Proof. exact (EQ_MP (@lem6933864 A s a f g' t') (@lem6933863 A s a f g' t')). Qed.
Lemma lem6933866 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term125 A s a f g' t' e'.
Proof. exact (@lem6933865 A s a f g' t' e'). Qed.
Lemma lem6933867 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term125 A s a f g' t' e') = (term126 A s a f g' t' e').
Proof. exact (eq_refl (term125 A s a f g' t' e')). Qed.
Lemma lem6933868 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term126 A s a f g' t' e'.
Proof. exact (EQ_MP (@lem6933867 A s a f g' t' e') (@lem6933866 A s a f g' t' e')). Qed.
Lemma lem6933870 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem6933792 A s x y) (@lem6933791 A s x y)). Qed.
Lemma lem6933871 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem6933870 A s x y). Qed.
Lemma lem6933872 {A : Type'} (s : A -> Prop) (a : A) : (term118 A s a) = (term127 A s a).
Proof. exact (@lem6933871 A s a a). Qed.
Lemma lem6933876 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem6933835 A a s) (@lem6933036 A a s h1)). Qed.
Lemma lem6933877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6933878 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term28 A a s) = (and True).
Proof. exact (MK_COMB (@lem6933877) (@lem6933876 A a s h1)). Qed.
Lemma lem6933880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6933881 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6933880 A x). Qed.
Lemma lem6933882 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem6933881 A a). Qed.
Lemma lem6933883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6933884 {A : Type'} (a : A) : (term76 A a) = (~ True).
Proof. exact (MK_COMB (@lem6933883) (@lem6933882 A a)). Qed.
Lemma lem6933886 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem6933887 {A : Type'} (a : A) : (term76 A a) = False.
Proof. exact (TRANS (@lem6933884 A a) (@lem6933886)). Qed.
Lemma lem6933888 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = (True /\ False).
Proof. exact (MK_COMB (@lem6933878 A a s h1) (@lem6933887 A a)). Qed.
Lemma lem6933890 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6933891 : (True /\ False) = False.
Proof. exact (@lem6933890 False). Qed.
Lemma lem6933892 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = False.
Proof. exact (TRANS (@lem6933888 A a s h1) (@lem6933891)). Qed.
Lemma lem6933893 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term118 A s a) = False.
Proof. exact (TRANS (@lem6933872 A s a) (@lem6933892 A a s h1)). Qed.
Lemma lem6933894 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (t' : nat) (e' : nat) : term128 A s a f t' e'.
Proof. exact (@lem6933868 A s a f False t' e'). Qed.
Lemma lem6933895 {A : Type'} (f : A -> nat) (t' : nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term129 A s a f t' e'.
Proof. exact (@lem6933894 A s a f t' e' (@lem6933893 A a s h1)). Qed.
Lemma lem6933899 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) : (term119 A s a f) = (term119 A s a f).
Proof. exact (eq_refl (term119 A s a f)). Qed.
Lemma lem6933900 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) : term130 A s a f.
Proof. exact (fun h0 : False => @lem6933899 A s a f). Qed.
Lemma lem6933901 {A : Type'} (f : A -> nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term131 A s a f e'.
Proof. exact (@lem6933895 A f (term119 A s a f) e' a s h1). Qed.
Lemma lem6933902 {A : Type'} (f : A -> nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term132 A s a f e'.
Proof. exact (@lem6933901 A f e' a s h1 (@lem6933900 A s a f)). Qed.
Lemma lem6933908 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) : (term120 A s a f) = (term120 A s a f).
Proof. exact (eq_refl (term120 A s a f)). Qed.
Lemma lem6933909 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) : term133 A s a f.
Proof. exact (fun h0 : ~ False => @lem6933908 A s a f). Qed.
Lemma lem6933910 {A : Type'} (f : A -> nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term134 A s a f.
Proof. exact (@lem6933902 A f (term120 A s a f) a s h1). Qed.
Lemma lem6933911 {A : Type'} (f : A -> nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a f) = (term135 A s a f).
Proof. exact (@lem6933910 A f a s h1 (@lem6933909 A s a f)). Qed.
Lemma lem6933913 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6933914 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6933913 nat t1 t2). Qed.
Lemma lem6933915 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) : (term135 A s a f) = (term120 A s a f).
Proof. exact (@lem6933914 (term119 A s a f) (term120 A s a f)). Qed.
Lemma lem6933916 {A : Type'} (f : A -> nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a f) = (term120 A s a f).
Proof. exact (TRANS (@lem6933911 A f a s h1) (@lem6933915 A s a f)). Qed.
Lemma lem6933917 {A : Type'} (f : A -> nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term110 A s a f) = (term120 A s a f).
Proof. exact (TRANS (@lem6933852 A a f s h1) (@lem6933916 A f a s h2)). Qed.
Lemma lem6933918 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6933919 {A : Type'} (f : A -> nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term136 A s a f) = (term137 A s a f).
Proof. exact (MK_COMB (@lem6933918) (@lem6933917 A f a s h1 h2)). Qed.
Lemma lem6933921 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term106 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6933811 _126525 x f s h0). Qed.
Lemma lem6933922 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) : term106 A x s f.
Proof. exact (@lem6933921 A x s f). Qed.
Lemma lem6933923 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) : term109 A s a g.
Proof. exact (@lem6933922 A a (@DELETE A s a) g). Qed.
Lemma lem6933925 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem6933798 A x s) (@lem6933797 A s x)). Qed.
Lemma lem6933926 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (@lem6933925 A x s). Qed.
Lemma lem6933927 {A : Type'} (a : A) (s : A -> Prop) : (term99 A s a) = (@FINITE A s).
Proof. exact (@lem6933926 A a s). Qed.
Lemma lem6933929 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6933821 A s) (@lem6933028 A s h1)). Qed.
Lemma lem6933930 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term99 A s a) = True.
Proof. exact (TRANS (@lem6933927 A a s) (@lem6933929 A s h1)). Qed.
Lemma lem6933931 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : True = (term99 A s a).
Proof. exact (SYM (@lem6933930 A a s h1)). Qed.
Lemma lem6933932 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : term99 A s a.
Proof. exact (EQ_MP (@lem6933931 A a s h1) (@lem0)). Qed.
Lemma lem6933933 {A : Type'} (a : A) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : (term110 A s a g) = (term111 A s a g).
Proof. exact (@lem6933923 A s a g (@lem6933932 A a s h1)). Qed.
Lemma lem6933935 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term112 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6933936 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term113 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6933935 _2963 g t e g' t' e'). Qed.
Lemma lem6933937 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term114 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6933936 _2963 g t e g' t'). Qed.
Lemma lem6933938 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term115 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6933937 _2963 g t e g'). Qed.
Lemma lem6933939 (g : Prop) (t : nat) (e : nat) : term116 g t e.
Proof. exact (@lem6933938 nat g t e). Qed.
Lemma lem6933940 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) : term117 A s a g.
Proof. exact (@lem6933939 (term118 A s a) (term119 A s a g) (term120 A s a g)). Qed.
Lemma lem6933941 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) : term121 A s a g g'.
Proof. exact (@lem6933940 A s a g g'). Qed.
Lemma lem6933942 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) : (term121 A s a g g') = (term122 A s a g g').
Proof. exact (eq_refl (term121 A s a g g')). Qed.
Lemma lem6933943 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) : term122 A s a g g'.
Proof. exact (EQ_MP (@lem6933942 A s a g g') (@lem6933941 A s a g g')). Qed.
Lemma lem6933944 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) (t' : nat) : term123 A s a g g' t'.
Proof. exact (@lem6933943 A s a g g' t'). Qed.
Lemma lem6933945 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) (t' : nat) : (term123 A s a g g' t') = (term124 A s a g g' t').
Proof. exact (eq_refl (term123 A s a g g' t')). Qed.
Lemma lem6933946 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) (t' : nat) : term124 A s a g g' t'.
Proof. exact (EQ_MP (@lem6933945 A s a g g' t') (@lem6933944 A s a g g' t')). Qed.
Lemma lem6933947 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term125 A s a g g' t' e'.
Proof. exact (@lem6933946 A s a g g' t' e'). Qed.
Lemma lem6933948 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term125 A s a g g' t' e') = (term126 A s a g g' t' e').
Proof. exact (eq_refl (term125 A s a g g' t' e')). Qed.
Lemma lem6933949 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (g' : Prop) (t' : nat) (e' : nat) : term126 A s a g g' t' e'.
Proof. exact (EQ_MP (@lem6933948 A s a g g' t' e') (@lem6933947 A s a g g' t' e')). Qed.
Lemma lem6933951 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem6933792 A s x y) (@lem6933791 A s x y)). Qed.
Lemma lem6933952 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem6933951 A s x y). Qed.
Lemma lem6933953 {A : Type'} (s : A -> Prop) (a : A) : (term118 A s a) = (term127 A s a).
Proof. exact (@lem6933952 A s a a). Qed.
Lemma lem6933957 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem6933835 A a s) (@lem6933036 A a s h1)). Qed.
Lemma lem6933958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6933959 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term28 A a s) = (and True).
Proof. exact (MK_COMB (@lem6933958) (@lem6933957 A a s h1)). Qed.
Lemma lem6933961 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6933962 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6933961 A x). Qed.
Lemma lem6933963 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem6933962 A a). Qed.
Lemma lem6933964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6933965 {A : Type'} (a : A) : (term76 A a) = (~ True).
Proof. exact (MK_COMB (@lem6933964) (@lem6933963 A a)). Qed.
Lemma lem6933967 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem6933968 {A : Type'} (a : A) : (term76 A a) = False.
Proof. exact (TRANS (@lem6933965 A a) (@lem6933967)). Qed.
Lemma lem6933969 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = (True /\ False).
Proof. exact (MK_COMB (@lem6933959 A a s h1) (@lem6933968 A a)). Qed.
Lemma lem6933971 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6933972 : (True /\ False) = False.
Proof. exact (@lem6933971 False). Qed.
Lemma lem6933973 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term127 A s a) = False.
Proof. exact (TRANS (@lem6933969 A a s h1) (@lem6933972)). Qed.
Lemma lem6933974 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term118 A s a) = False.
Proof. exact (TRANS (@lem6933953 A s a) (@lem6933973 A a s h1)). Qed.
Lemma lem6933975 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) (t' : nat) (e' : nat) : term128 A s a g t' e'.
Proof. exact (@lem6933949 A s a g False t' e'). Qed.
Lemma lem6933976 {A : Type'} (g : A -> nat) (t' : nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term129 A s a g t' e'.
Proof. exact (@lem6933975 A s a g t' e' (@lem6933974 A a s h1)). Qed.
Lemma lem6933980 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) : (term119 A s a g) = (term119 A s a g).
Proof. exact (eq_refl (term119 A s a g)). Qed.
Lemma lem6933981 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) : term130 A s a g.
Proof. exact (fun h0 : False => @lem6933980 A s a g). Qed.
Lemma lem6933982 {A : Type'} (g : A -> nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term131 A s a g e'.
Proof. exact (@lem6933976 A g (term119 A s a g) e' a s h1). Qed.
Lemma lem6933983 {A : Type'} (g : A -> nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term132 A s a g e'.
Proof. exact (@lem6933982 A g e' a s h1 (@lem6933981 A s a g)). Qed.
Lemma lem6933989 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) : (term120 A s a g) = (term120 A s a g).
Proof. exact (eq_refl (term120 A s a g)). Qed.
Lemma lem6933990 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) : term133 A s a g.
Proof. exact (fun h0 : ~ False => @lem6933989 A s a g). Qed.
Lemma lem6933991 {A : Type'} (g : A -> nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term134 A s a g.
Proof. exact (@lem6933983 A g (term120 A s a g) a s h1). Qed.
Lemma lem6933992 {A : Type'} (g : A -> nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a g) = (term135 A s a g).
Proof. exact (@lem6933991 A g a s h1 (@lem6933990 A s a g)). Qed.
Lemma lem6933994 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6933995 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6933994 nat t1 t2). Qed.
Lemma lem6933996 {A : Type'} (s : A -> Prop) (a : A) (g : A -> nat) : (term135 A s a g) = (term120 A s a g).
Proof. exact (@lem6933995 (term119 A s a g) (term120 A s a g)). Qed.
Lemma lem6933997 {A : Type'} (g : A -> nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A s a g) = (term120 A s a g).
Proof. exact (TRANS (@lem6933992 A g a s h1) (@lem6933996 A s a g)). Qed.
Lemma lem6933998 {A : Type'} (g : A -> nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term110 A s a g) = (term120 A s a g).
Proof. exact (TRANS (@lem6933933 A a g s h1) (@lem6933997 A g a s h2)). Qed.
Lemma lem6933999 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term10 A f s a g) = (term138 A f s a g).
Proof. exact (MK_COMB (@lem6933919 A f a s h1 h2) (@lem6933998 A g a s h1 h2)). Qed.
Lemma lem6934000 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term138 A f s a g) = (term10 A f s a g).
Proof. exact (SYM (@lem6933999 A f g a s h1 h2)). Qed.
Lemma lem6934001 {A : Type'} (s : A -> Prop) : term96 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem6934002 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (eq_refl (term96 A s)). Qed.
Lemma lem6934003 {A : Type'} (s : A -> Prop) : term97 A s.
Proof. exact (EQ_MP (@lem6934002 A s) (@lem6934001 A s)). Qed.
Lemma lem6934004 {A : Type'} (s : A -> Prop) (x : A) : term98 A s x.
Proof. exact (@lem6934003 A s x). Qed.
Lemma lem6934005 {A : Type'} (x : A) (s : A -> Prop) : (term98 A s x) = ((term99 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term98 A s x)). Qed.
Lemma lem6934007 {A : Type'} (s : A -> Prop) : term91 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem6934008 {A : Type'} (s : A -> Prop) : (term91 A s) = (term92 A s).
Proof. exact (eq_refl (term91 A s)). Qed.
Lemma lem6934009 {A : Type'} (s : A -> Prop) : term92 A s.
Proof. exact (EQ_MP (@lem6934008 A s) (@lem6934007 A s)). Qed.
Lemma lem6934010 {A : Type'} (s : A -> Prop) (x : A) : term93 A s x.
Proof. exact (@lem6934009 A s x). Qed.
Lemma lem6934011 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term94 A s x).
Proof. exact (eq_refl (term93 A s x)). Qed.
Lemma lem6934012 {A : Type'} (s : A -> Prop) (x : A) : term94 A s x.
Proof. exact (EQ_MP (@lem6934011 A s x) (@lem6934010 A s x)). Qed.
Lemma lem6934013 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term95 A s x y.
Proof. exact (@lem6934012 A s x y). Qed.
Lemma lem6934014 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term95 A s x y) = ((term26 A x s y) = (term27 A s x y)).
Proof. exact (eq_refl (term95 A s x y)). Qed.
Lemma lem6934016 {_127006 : Type'} (f : _127006 -> nat) : term139 _127006 f.
Proof. exact (@lem6933015 _127006 f). Qed.
Lemma lem6934017 {_127006 : Type'} (f : _127006 -> nat) : (term139 _127006 f) = (term140 _127006 f).
Proof. exact (eq_refl (term139 _127006 f)). Qed.
Lemma lem6934018 {_127006 : Type'} (f : _127006 -> nat) : term140 _127006 f.
Proof. exact (EQ_MP (@lem6934017 _127006 f) (@lem6934016 _127006 f)). Qed.
Lemma lem6934019 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term141 _127006 f g.
Proof. exact (@lem6934018 _127006 f g). Qed.
Lemma lem6934020 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term141 _127006 f g) = (term142 _127006 f g).
Proof. exact (eq_refl (term141 _127006 f g)). Qed.
Lemma lem6934021 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term142 _127006 f g.
Proof. exact (EQ_MP (@lem6934020 _127006 f g) (@lem6934019 _127006 f g)). Qed.
Lemma lem6934022 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (s : _127006 -> Prop) : term143 _127006 f g s.
Proof. exact (@lem6934021 _127006 f g s). Qed.
Lemma lem6934023 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term143 _127006 f g s) = (term144 _127006 f s g).
Proof. exact (eq_refl (term143 _127006 f g s)). Qed.
Lemma lem6934024 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term144 _127006 f s g.
Proof. exact (EQ_MP (@lem6934023 _127006 f s g) (@lem6934022 _127006 f g s)). Qed.
Lemma lem6934025 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term145 _127006 s f g) : term145 _127006 s f g.
Proof. exact (h1). Qed.
Lemma lem6934026 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term145 _127006 s f g) : term146 _127006 f s g.
Proof. exact (@lem6934024 _127006 f s g (@lem6934025 _127006 s f g h1)). Qed.
Lemma lem6934027 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term146 _127006 f s g) = ((term146 _127006 f s g) = True).
Proof. exact (@lem7 (term146 _127006 f s g)). Qed.
Lemma lem6934028 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term145 _127006 s f g) : (term146 _127006 f s g) = True.
Proof. exact (EQ_MP (@lem6934027 _127006 f s g) (@lem6934026 _127006 s f g h1)). Qed.
Lemma lem6934034 (m : nat) : term147 m.
Proof. exact (@lem101790 m). Qed.
Lemma lem6934035 (m : nat) : (term147 m) = (term148 m).
Proof. exact (eq_refl (term147 m)). Qed.
Lemma lem6934036 (m : nat) : term148 m.
Proof. exact (EQ_MP (@lem6934035 m) (@lem6934034 m)). Qed.
Lemma lem6934037 (m : nat) (n : nat) : term149 m n.
Proof. exact (@lem6934036 m n). Qed.
Lemma lem6934038 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (eq_refl (term149 m n)). Qed.
Lemma lem6934039 (m : nat) (n : nat) : term150 m n.
Proof. exact (EQ_MP (@lem6934038 m n) (@lem6934037 m n)). Qed.
Lemma lem6934040 (m : nat) (n : nat) (p : nat) : term151 m n p.
Proof. exact (@lem6934039 m n p). Qed.
Lemma lem6934041 (m : nat) (n : nat) (p : nat) : (term151 m n p) = (term152 m n p).
Proof. exact (eq_refl (term151 m n p)). Qed.
Lemma lem6934042 (m : nat) (n : nat) (p : nat) : term152 m n p.
Proof. exact (EQ_MP (@lem6934041 m n p) (@lem6934040 m n p)). Qed.
Lemma lem6934043 (m : nat) (n : nat) (p : nat) (q : nat) : term153 m n p q.
Proof. exact (@lem6934042 m n p q). Qed.
Lemma lem6934044 (m : nat) (n : nat) (p : nat) (q : nat) : (term153 m n p q) = (term154 m n p q).
Proof. exact (eq_refl (term153 m n p q)). Qed.
Lemma lem6934045 (m : nat) (n : nat) (p : nat) (q : nat) : term154 m n p q.
Proof. exact (EQ_MP (@lem6934044 m n p q) (@lem6934043 m n p q)). Qed.
Lemma lem6934046 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term155 m p n q) : term155 m p n q.
Proof. exact (h1). Qed.
Lemma lem6934047 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term155 m p n q) : term156 m n p q.
Proof. exact (@lem6934045 m n p q (@lem6934046 m p n q h1)). Qed.
Lemma lem6934048 (m : nat) (n : nat) (p : nat) (q : nat) : (term156 m n p q) = ((term156 m n p q) = True).
Proof. exact (@lem7 (term156 m n p q)). Qed.
Lemma lem6934049 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term155 m p n q) : (term156 m n p q) = True.
Proof. exact (EQ_MP (@lem6934048 m n p q) (@lem6934047 m p n q h1)). Qed.
Lemma lem6934055 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6934057 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : term157 A s f g x.
Proof. exact (@lem6933031 A s f g h1 x). Qed.
Lemma lem6934058 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (x : A) : (term157 A s f g x) = (term158 A s f g x).
Proof. exact (eq_refl (term157 A s f g x)). Qed.
Lemma lem6934059 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : term158 A s f g x.
Proof. exact (EQ_MP (@lem6934058 A s f g x) (@lem6934057 A x s f g h1)). Qed.
Lemma lem6934060 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6934061 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @IN A x s) : term159 A f g x.
Proof. exact (@lem6934059 A x s f g h1 (@lem6934060 A x s h2)). Qed.
Lemma lem6934062 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) : (term159 A f g x) = ((term159 A f g x) = True).
Proof. exact (@lem7 (term159 A f g x)). Qed.
Lemma lem6934063 {A : Type'} (f : A -> nat) (g : A -> nat) (x : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @IN A x s) : (term159 A f g x) = True.
Proof. exact (EQ_MP (@lem6934062 A f g x) (@lem6934061 A f g x s h1 h2)). Qed.
Lemma lem6934071 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) : (term5 A f g a) = ((term5 A f g a) = True).
Proof. exact (@lem7 (term5 A f g a)). Qed.
Lemma lem6934074 (m : nat) (n : nat) (p : nat) (q : nat) : term160 m n p q.
Proof. exact (fun h0 : term155 m p n q => @lem6934049 m p n q h0). Qed.
Lemma lem6934075 {A : Type'} (f : A -> nat) (s : A -> Prop) (a : A) (g : A -> nat) : term161 A f s a g.
Proof. exact (@lem6934074 (f a) (term119 A s a f) (g a) (term119 A s a g)). Qed.
Lemma lem6934079 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (h1 : term5 A f g a) : (term5 A f g a) = True.
Proof. exact (EQ_MP (@lem6934071 A f g a) (@lem6933035 A f g a h1)). Qed.
Lemma lem6934080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6934081 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (h1 : term5 A f g a) : (term162 A f g a) = (and True).
Proof. exact (MK_COMB (@lem6934080) (@lem6934079 A f g a h1)). Qed.
Lemma lem6934083 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term163 _127006 f s g.
Proof. exact (fun h0 : term145 _127006 s f g => @lem6934028 _127006 s f g h0). Qed.
Lemma lem6934084 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term163 A f s g.
Proof. exact (@lem6934083 A f s g). Qed.
Lemma lem6934085 {A : Type'} (f : A -> nat) (s : A -> Prop) (a : A) (g : A -> nat) : term164 A f s a g.
Proof. exact (@lem6934084 A f (@DELETE A s a) g). Qed.
Lemma lem6934089 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem6934005 A x s) (@lem6934004 A s x)). Qed.
Lemma lem6934090 {A : Type'} (x : A) (s : A -> Prop) : (term99 A s x) = (@FINITE A s).
Proof. exact (@lem6934089 A x s). Qed.
Lemma lem6934091 {A : Type'} (a : A) (s : A -> Prop) : (term99 A s a) = (@FINITE A s).
Proof. exact (@lem6934090 A a s). Qed.
Lemma lem6934093 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6934055 A s) (@lem6933028 A s h1)). Qed.
Lemma lem6934094 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term99 A s a) = True.
Proof. exact (TRANS (@lem6934091 A a s) (@lem6934093 A s h1)). Qed.
Lemma lem6934095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6934096 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term165 A s a) = (and True).
Proof. exact (MK_COMB (@lem6934095) (@lem6934094 A a s h1)). Qed.
Lemma lem6934104 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6934105 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem6934104 p q p' q'). Qed.
Lemma lem6934106 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem6934105 p q p'). Qed.
Lemma lem6934107 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g : A -> nat) (x : A) : term169 A s a f g x.
Proof. exact (@lem6934106 (term26 A x s a) (term159 A f g x)). Qed.
Lemma lem6934108 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) : term170 A s a f g x p'.
Proof. exact (@lem6934107 A s a f g x p'). Qed.
Lemma lem6934109 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) : (term170 A s a f g x p') = (term171 A s a f g x p').
Proof. exact (eq_refl (term170 A s a f g x p')). Qed.
Lemma lem6934110 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) : term171 A s a f g x p'.
Proof. exact (EQ_MP (@lem6934109 A s a f g x p') (@lem6934108 A s a f g x p')). Qed.
Lemma lem6934111 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term172 A s a f g x p' q'.
Proof. exact (@lem6934110 A s a f g x p' q'). Qed.
Lemma lem6934112 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) (q' : Prop) : (term172 A s a f g x p' q') = (term173 A s a f g x p' q').
Proof. exact (eq_refl (term172 A s a f g x p' q')). Qed.
Lemma lem6934113 {A : Type'} (s : A -> Prop) (a : A) (f : A -> nat) (g : A -> nat) (x : A) (p' : Prop) (q' : Prop) : term173 A s a f g x p' q'.
Proof. exact (EQ_MP (@lem6934112 A s a f g x p' q') (@lem6934111 A s a f g x p' q')). Qed.
Lemma lem6934115 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem6934014 A s x y) (@lem6934013 A s x y)). Qed.
Lemma lem6934116 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem6934115 A s x y). Qed.
Lemma lem6934117 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term26 A x s a) = (term27 A s x a).
Proof. exact (@lem6934116 A s x a). Qed.
Lemma lem6934122 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (x : A) (a : A) (q' : Prop) : term174 A f g s x a q'.
Proof. exact (@lem6934113 A s a f g x (term27 A s x a) q'). Qed.
Lemma lem6934123 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (x : A) (a : A) (q' : Prop) : term175 A f g s x a q'.
Proof. exact (@lem6934122 A f g s x a q' (@lem6934117 A s x a)). Qed.
Lemma lem6934124 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : term27 A s x a.
Proof. exact (h1). Qed.
Lemma lem6934139 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : @IN A x s.
Proof. exact (proj1 (@lem6934124 A s x a h1)). Qed.
Lemma lem6934140 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem6934143 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : term176 A s f g x.
Proof. exact (fun h0 : @IN A x s => @lem6934063 A f g x s h1 h0). Qed.
Lemma lem6934144 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : term176 A s f g x.
Proof. exact (@lem6934143 A x s f g h1). Qed.
Lemma lem6934146 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem6934140 A x s) (@lem6934139 A s x a h1)). Qed.
Lemma lem6934147 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : True = (@IN A x s).
Proof. exact (SYM (@lem6934146 A s x a h1)). Qed.
Lemma lem6934148 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term27 A s x a) : @IN A x s.
Proof. exact (EQ_MP (@lem6934147 A s x a h1) (@lem0)). Qed.
Lemma lem6934149 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (x : A) (a : A) (h1 : term3 A s f g) (h2 : term27 A s x a) : (term159 A f g x) = True.
Proof. exact (@lem6934144 A x s f g h1 (@lem6934148 A s x a h2)). Qed.
Lemma lem6934150 {A : Type'} (a : A) (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : term177 A s a f g x.
Proof. exact (fun h0 : term27 A s x a => @lem6934149 A f g s x a h1 h0). Qed.
Lemma lem6934151 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (x : A) (a : A) : term178 A f g s x a.
Proof. exact (@lem6934123 A f g s x a True). Qed.
Lemma lem6934152 {A : Type'} (x : A) (a : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : (term179 A s a f g x) = (term180 A s x a).
Proof. exact (@lem6934151 A f g s x a (@lem6934150 A a x s f g h1)). Qed.
Lemma lem6934154 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6934155 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term180 A s x a) = True.
Proof. exact (@lem6934154 (term27 A s x a)). Qed.
Lemma lem6934156 {A : Type'} (a : A) (x : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : (term179 A s a f g x) = True.
Proof. exact (TRANS (@lem6934152 A x a s f g h1) (@lem6934155 A s x a)). Qed.
Lemma lem6934157 {A : Type'} (a : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : (term181 A s a f g) = (term182 A).
Proof. exact (fun_ext (fun x : A => @lem6934156 A a x s f g h1)). Qed.
Lemma lem6934158 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6934159 {A : Type'} (a : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : (term183 A s a f g) = (term184 A).
Proof. exact (MK_COMB (@lem6934158 A) (@lem6934157 A a s f g h1)). Qed.
Lemma lem6934161 {A : Type'} (t : Prop) : (term185 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6934162 {A : Type'} (t : Prop) : (term185 A t) = t.
Proof. exact (@lem6934161 A t). Qed.
Lemma lem6934163 {A : Type'} : (term184 A) = True.
Proof. exact (@lem6934162 A True). Qed.
Lemma lem6934164 {A : Type'} (a : A) (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) : (term183 A s a f g) = True.
Proof. exact (TRANS (@lem6934159 A a s f g h1) (@lem6934163 A)). Qed.
Lemma lem6934165 {A : Type'} (a : A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : (term186 A s a f g) = (True /\ True).
Proof. exact (MK_COMB (@lem6934096 A a s h2) (@lem6934164 A a s f g h1)). Qed.
Lemma lem6934167 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6934168 : (True /\ True) = True.
Proof. exact (@lem6934167 True). Qed.
Lemma lem6934169 {A : Type'} (a : A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : (term186 A s a f g) = True.
Proof. exact (TRANS (@lem6934165 A a f g s h1 h2) (@lem6934168)). Qed.
Lemma lem6934170 {A : Type'} (a : A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : True = (term186 A s a f g).
Proof. exact (SYM (@lem6934169 A a f g s h1 h2)). Qed.
Lemma lem6934171 {A : Type'} (a : A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : term186 A s a f g.
Proof. exact (EQ_MP (@lem6934170 A a f g s h1 h2) (@lem0)). Qed.
Lemma lem6934172 {A : Type'} (a : A) (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : (term187 A f s a g) = True.
Proof. exact (@lem6934085 A f s a g (@lem6934171 A a f g s h1 h2)). Qed.
Lemma lem6934173 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : (term188 A f s a g) = (True /\ True).
Proof. exact (MK_COMB (@lem6934081 A f g a h3) (@lem6934172 A a f g s h1 h2)). Qed.
Lemma lem6934175 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6934176 : (True /\ True) = True.
Proof. exact (@lem6934175 True). Qed.
Lemma lem6934177 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : (term188 A f s a g) = True.
Proof. exact (TRANS (@lem6934173 A s f g a h1 h2 h3) (@lem6934176)). Qed.
Lemma lem6934178 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : True = (term188 A f s a g).
Proof. exact (SYM (@lem6934177 A s f g a h1 h2 h3)). Qed.
Lemma lem6934179 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : term188 A f s a g.
Proof. exact (EQ_MP (@lem6934178 A s f g a h1 h2 h3) (@lem0)). Qed.
Lemma lem6934180 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : (term138 A f s a g) = True.
Proof. exact (@lem6934075 A f s a g (@lem6934179 A s f g a h1 h2 h3)). Qed.
Lemma lem6934181 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : True = (term138 A f s a g).
Proof. exact (SYM (@lem6934180 A s f g a h1 h2 h3)). Qed.
Lemma lem6934182 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) : term138 A f s a g.
Proof. exact (EQ_MP (@lem6934181 A s f g a h1 h2 h3) (@lem0)). Qed.
Lemma lem6934183 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : @IN A a s) : term10 A f s a g.
Proof. exact (EQ_MP (@lem6934000 A f g a s h2 h4) (@lem6934182 A s f g a h1 h2 h3)). Qed.
Lemma lem6934184 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : s = (term6 A s a)) (h5 : @IN A a s) : term12 A f s g.
Proof. exact (EQ_MP (@lem6933050 A f g s a h4) (@lem6934183 A f g a s h1 h2 h3 h5)). Qed.
Lemma lem6934185 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : @IN A a s) : (s = (term6 A s a)) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : s = (term6 A s a) => @lem6934184 A f g a s h1 h2 h3 h5 h4) (fun h5 : term12 A f s g => @lem6933784 A a s h4)). Qed.
Lemma lem6934186 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : @IN A a s) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934185 A f g a s h1 h2 h3 h4) (@lem6933784 A a s h4)). Qed.
Lemma lem6934187 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term4 A s f g a) : term5 A f g a.
Proof. exact (proj2 (@lem6933034 A s f g a h1)). Qed.
Lemma lem6934188 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term4 A s f g a) : @IN A a s.
Proof. exact (proj1 (@lem6933034 A s f g a h1)). Qed.
Lemma lem6934189 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : @IN A a s) : (term5 A f g a) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : term5 A f g a => @lem6934186 A f g a s h1 h2 h3 h4) (fun h5 : term12 A f s g => @lem6933035 A f g a h3)). Qed.
Lemma lem6934190 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : @IN A a s) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934189 A f g a s h1 h2 h3 h4) (@lem6933035 A f g a h3)). Qed.
Lemma lem6934191 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : @IN A a s) : (@IN A a s) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem6934190 A f g a s h1 h2 h3 h4) (fun h5 : term12 A f s g => @lem6933036 A a s h4)). Qed.
Lemma lem6934192 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term5 A f g a) (h4 : @IN A a s) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934191 A f g a s h1 h2 h3 h4) (@lem6933036 A a s h4)). Qed.
Lemma lem6934193 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) (h4 : @IN A a s) : (term5 A f g a) = (term12 A f s g).
Proof. exact (prop_ext (fun h5 : term5 A f g a => @lem6934192 A f g a s h1 h2 h5 h4) (fun h5 : term12 A f s g => @lem6934187 A s f g a h3)). Qed.
Lemma lem6934194 {A : Type'} (f : A -> nat) (g : A -> nat) (a : A) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) (h4 : @IN A a s) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934193 A f g a s h1 h2 h3 h4) (@lem6934187 A s f g a h3)). Qed.
Lemma lem6934195 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) : (@IN A a s) = (term12 A f s g).
Proof. exact (prop_ext (fun h4 : @IN A a s => @lem6934194 A f g a s h1 h2 h3 h4) (fun h4 : term12 A f s g => @lem6934188 A s f g a h3)). Qed.
Lemma lem6934196 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (a : A) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term4 A s f g a) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934195 A s f g a h1 h2 h3) (@lem6934188 A s f g a h3)). Qed.
Lemma lem6934197 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : term12 A f s g.
Proof. exact (ex_elim (@lem6933033 A s f g h2) (fun a : A => fun h0 : term189 A s f g a => @lem6934196 A s f g a h1 h3 h0)). Qed.
Lemma lem6934198 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : @FINITE A s) : term190 A f s g.
Proof. exact (fun h0 : term2 A s f g => @lem6934197 A f g s h1 h0 h2). Qed.
Lemma lem6934199 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term1 A s f g) : term2 A s f g.
Proof. exact (proj2 (@lem6933029 A s f g h1)). Qed.
Lemma lem6934200 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term1 A s f g) : term3 A s f g.
Proof. exact (proj1 (@lem6933029 A s f g h1)). Qed.
Lemma lem6934201 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : term12 A f s g.
Proof. exact (@lem6934198 A f g s h1 h3 (@lem6933030 A s f g h2)). Qed.
Lemma lem6934202 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : (term3 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h4 : term3 A s f g => @lem6934201 A f g s h1 h2 h3) (fun h4 : term12 A f s g => @lem6933031 A s f g h1)). Qed.
Lemma lem6934203 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : term3 A s f g) (h2 : term2 A s f g) (h3 : @FINITE A s) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934202 A f g s h1 h2 h3) (@lem6933031 A s f g h1)). Qed.
Lemma lem6934204 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term1 A s f g) : (term2 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h4 : term2 A s f g => @lem6934203 A f g s h1 h4 h2) (fun h4 : term12 A f s g => @lem6934199 A s f g h3)). Qed.
Lemma lem6934205 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term3 A s f g) (h2 : @FINITE A s) (h3 : term1 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934204 A s f g h1 h2 h3) (@lem6934199 A s f g h3)). Qed.
Lemma lem6934206 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : @FINITE A s) (h2 : term1 A s f g) : (term3 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h3 : term3 A s f g => @lem6934205 A s f g h3 h1 h2) (fun h3 : term12 A f s g => @lem6934200 A s f g h2)). Qed.
Lemma lem6934207 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : @FINITE A s) (h2 : term1 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934206 A s f g h1 h2) (@lem6934200 A s f g h2)). Qed.
Lemma lem6934208 {A : Type'} (f : A -> nat) (g : A -> nat) (s : A -> Prop) (h1 : @FINITE A s) : term191 A f s g.
Proof. exact (fun h0 : term1 A s f g => @lem6934207 A s f g h1 h0). Qed.
Lemma lem6934209 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term0 A s f g) : term1 A s f g.
Proof. exact (proj2 (@lem6933026 A s f g h1)). Qed.
Lemma lem6934210 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term0 A s f g) : @FINITE A s.
Proof. exact (proj1 (@lem6933026 A s f g h1)). Qed.
Lemma lem6934211 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : @FINITE A s) (h2 : term1 A s f g) : term12 A f s g.
Proof. exact (@lem6934208 A f g s h1 (@lem6933027 A s f g h2)). Qed.
Lemma lem6934212 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : @FINITE A s) (h2 : term1 A s f g) : (@FINITE A s) = (term12 A f s g).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6934211 A s f g h1 h2) (fun h3 : term12 A f s g => @lem6933028 A s h1)). Qed.
Lemma lem6934213 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : @FINITE A s) (h2 : term1 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934212 A s f g h1 h2) (@lem6933028 A s h1)). Qed.
Lemma lem6934214 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : @FINITE A s) (h2 : term0 A s f g) : (term1 A s f g) = (term12 A f s g).
Proof. exact (prop_ext (fun h3 : term1 A s f g => @lem6934213 A s f g h1 h3) (fun h3 : term12 A f s g => @lem6934209 A s f g h2)). Qed.
Lemma lem6934215 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : @FINITE A s) (h2 : term0 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934214 A s f g h1 h2) (@lem6934209 A s f g h2)). Qed.
Lemma lem6934216 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term0 A s f g) : (@FINITE A s) = (term12 A f s g).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem6934215 A s f g h2 h1) (fun h2 : term12 A f s g => @lem6934210 A s f g h1)). Qed.
Lemma lem6934217 {A : Type'} (s : A -> Prop) (f : A -> nat) (g : A -> nat) (h1 : term0 A s f g) : term12 A f s g.
Proof. exact (EQ_MP (@lem6934216 A s f g h1) (@lem6934210 A s f g h1)). Qed.
Lemma lem6934218 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term192 A f s g.
Proof. exact (fun h0 : term0 A s f g => @lem6934217 A s f g h0). Qed.
Lemma lem6934223 {A : Type'} (f : A -> nat) (g : A -> nat) : term193 A f g.
Proof. exact (fun s : A -> Prop => @lem6934218 A f s g). Qed.
Lemma lem6934228 {A : Type'} (f : A -> nat) : term194 A f.
Proof. exact (fun g : A -> nat => @lem6934223 A f g). Qed.
Lemma lem6934233 {A : Type'} : term195 A.
Proof. exact (fun f : A -> nat => @lem6934228 A f). Qed.
