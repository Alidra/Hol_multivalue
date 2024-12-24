Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_UNION_RZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_DIFF_spec.
Require Import IN_UNION_spec.
Require Import SUBSET_spec.
Require Import SUM_SUPERSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem7125064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7125065 {_133271 : Type'} (s : _133271 -> Prop) (t : _133271 -> Prop) : (s = t) = (term0 _133271 s t).
Proof. exact (@lem7125064 _133271 s t). Qed.
Lemma lem7125066 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : ((@UNION _133271 u v) = (term1 _133271 v u)) = (term2 _133271 v u).
Proof. exact (@lem7125065 _133271 (@UNION _133271 u v) (term1 _133271 v u)). Qed.
Lemma lem7125075 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term2 _133271 v u) = ((@UNION _133271 u v) = (term1 _133271 v u)).
Proof. exact (SYM (@lem7125066 _133271 v u)). Qed.
Lemma lem7125083 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A x s t) = (term4 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem7125084 {_133271 : Type'} (s : _133271 -> Prop) (x : _133271) (t : _133271 -> Prop) : (term3 _133271 x s t) = (term4 _133271 s x t).
Proof. exact (@lem7125083 _133271 s x t). Qed.
Lemma lem7125085 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (v : _133271 -> Prop) : (term3 _133271 x u v) = (term4 _133271 u x v).
Proof. exact (@lem7125084 _133271 u x v). Qed.
Lemma lem7125089 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7125090 {_133271 : Type'} (P : _133271 -> Prop) (x : _133271) : (@IN _133271 x P) = (P x).
Proof. exact (@lem7125089 _133271 P x). Qed.
Lemma lem7125091 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (@IN _133271 x u) = (u x).
Proof. exact (@lem7125090 _133271 u x). Qed.
Lemma lem7125092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7125093 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term5 _133271 x u) = (term6 _133271 u x).
Proof. exact (MK_COMB (@lem7125092) (@lem7125091 _133271 u x)). Qed.
Lemma lem7125095 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7125096 {_133271 : Type'} (P : _133271 -> Prop) (x : _133271) : (@IN _133271 x P) = (P x).
Proof. exact (@lem7125095 _133271 P x). Qed.
Lemma lem7125097 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (@IN _133271 x v) = (v x).
Proof. exact (@lem7125096 _133271 v x). Qed.
Lemma lem7125098 {_133271 : Type'} (u : _133271 -> Prop) (v : _133271 -> Prop) (x : _133271) : (term4 _133271 u x v) = (term7 _133271 u v x).
Proof. exact (MK_COMB (@lem7125093 _133271 u x) (@lem7125097 _133271 v x)). Qed.
Lemma lem7125101 {_133271 : Type'} (u : _133271 -> Prop) (v : _133271 -> Prop) (x : _133271) : (term3 _133271 x u v) = (term7 _133271 u v x).
Proof. exact (TRANS (@lem7125085 _133271 u x v) (@lem7125098 _133271 u v x)). Qed.
Lemma lem7125102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7125103 {_133271 : Type'} (u : _133271 -> Prop) (v : _133271 -> Prop) (x : _133271) : (term8 _133271 x u v) = (term9 _133271 u v x).
Proof. exact (MK_COMB (@lem7125102) (@lem7125101 _133271 u v x)). Qed.
Lemma lem7125105 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term3 A x s t) = (term4 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem7125106 {_133271 : Type'} (s : _133271 -> Prop) (x : _133271) (t : _133271 -> Prop) : (term3 _133271 x s t) = (term4 _133271 s x t).
Proof. exact (@lem7125105 _133271 s x t). Qed.
Lemma lem7125107 {_133271 : Type'} (x : _133271) (v : _133271 -> Prop) (u : _133271 -> Prop) : (term10 _133271 x v u) = (term11 _133271 x v u).
Proof. exact (@lem7125106 _133271 u x (@DIFF _133271 v u)). Qed.
Lemma lem7125111 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7125112 {_133271 : Type'} (P : _133271 -> Prop) (x : _133271) : (@IN _133271 x P) = (P x).
Proof. exact (@lem7125111 _133271 P x). Qed.
Lemma lem7125113 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (@IN _133271 x u) = (u x).
Proof. exact (@lem7125112 _133271 u x). Qed.
Lemma lem7125114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7125115 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term5 _133271 x u) = (term6 _133271 u x).
Proof. exact (MK_COMB (@lem7125114) (@lem7125113 _133271 u x)). Qed.
Lemma lem7125117 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7125118 {_133271 : Type'} (s : _133271 -> Prop) (x : _133271) (t : _133271 -> Prop) : (term12 _133271 x s t) = (term13 _133271 s x t).
Proof. exact (@lem7125117 _133271 s x t). Qed.
Lemma lem7125119 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (u : _133271 -> Prop) : (term12 _133271 x v u) = (term13 _133271 v x u).
Proof. exact (@lem7125118 _133271 v x u). Qed.
Lemma lem7125123 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7125124 {_133271 : Type'} (P : _133271 -> Prop) (x : _133271) : (@IN _133271 x P) = (P x).
Proof. exact (@lem7125123 _133271 P x). Qed.
Lemma lem7125125 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (@IN _133271 x v) = (v x).
Proof. exact (@lem7125124 _133271 v x). Qed.
Lemma lem7125126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7125127 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (term14 _133271 x v) = (term15 _133271 v x).
Proof. exact (MK_COMB (@lem7125126) (@lem7125125 _133271 v x)). Qed.
Lemma lem7125129 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7125130 {_133271 : Type'} (P : _133271 -> Prop) (x : _133271) : (@IN _133271 x P) = (P x).
Proof. exact (@lem7125129 _133271 P x). Qed.
Lemma lem7125131 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (@IN _133271 x u) = (u x).
Proof. exact (@lem7125130 _133271 u x). Qed.
Lemma lem7125132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7125133 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term16 _133271 x u) = (term17 _133271 u x).
Proof. exact (MK_COMB (@lem7125132) (@lem7125131 _133271 u x)). Qed.
Lemma lem7125134 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term13 _133271 v x u) = (term18 _133271 v u x).
Proof. exact (MK_COMB (@lem7125127 _133271 v x) (@lem7125133 _133271 u x)). Qed.
Lemma lem7125137 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term12 _133271 x v u) = (term18 _133271 v u x).
Proof. exact (TRANS (@lem7125119 _133271 v x u) (@lem7125134 _133271 v u x)). Qed.
Lemma lem7125138 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term11 _133271 x v u) = (term19 _133271 v u x).
Proof. exact (MK_COMB (@lem7125115 _133271 u x) (@lem7125137 _133271 v u x)). Qed.
Lemma lem7125141 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term10 _133271 x v u) = (term19 _133271 v u x).
Proof. exact (TRANS (@lem7125107 _133271 x v u) (@lem7125138 _133271 v u x)). Qed.
Lemma lem7125142 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : ((term3 _133271 x u v) = (term10 _133271 x v u)) = ((term7 _133271 u v x) = (term19 _133271 v u x)).
Proof. exact (MK_COMB (@lem7125103 _133271 u v x) (@lem7125141 _133271 v u x)). Qed.
Lemma lem7125145 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term20 _133271 v u) = (term21 _133271 v u).
Proof. exact (fun_ext (fun x : _133271 => @lem7125142 _133271 v u x)). Qed.
Lemma lem7125146 {_133271 : Type'} : (@all _133271) = (@all _133271).
Proof. exact (eq_refl (@all _133271)). Qed.
Lemma lem7125147 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term2 _133271 v u) = (term22 _133271 v u).
Proof. exact (MK_COMB (@lem7125146 _133271) (@lem7125145 _133271 v u)). Qed.
Lemma lem7125152 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term22 _133271 v u) = (term2 _133271 v u).
Proof. exact (SYM (@lem7125147 _133271 v u)). Qed.
Lemma lem7125154 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7125155 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term22 _133271 v u) = (term24 _133271 v u).
Proof. exact (@lem7125154 (term22 _133271 v u)). Qed.
Lemma lem7125156 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term24 _133271 v u) = (term22 _133271 v u).
Proof. exact (SYM (@lem7125155 _133271 v u)). Qed.
Lemma lem7125157 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term25 _133271 v u) : term25 _133271 v u.
Proof. exact (h1). Qed.
Lemma lem7125160 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term24 _133271 v u) : term24 _133271 v u.
Proof. exact (h1). Qed.
Lemma lem7125161 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term26 _133271 v u.
Proof. exact (fun h0 : term24 _133271 v u => @lem7125160 _133271 v u h0). Qed.
Lemma lem7125162 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term26 _133271 v u) : term26 _133271 v u.
Proof. exact (h1). Qed.
Lemma lem7125163 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term24 _133271 v u) : term24 _133271 v u.
Proof. exact (h1). Qed.
Lemma lem7125164 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term24 _133271 v u) (h2 : term26 _133271 v u) : term24 _133271 v u.
Proof. exact (@lem7125162 _133271 v u h2 (@lem7125163 _133271 v u h1)). Qed.
Lemma lem7125165 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term24 _133271 v u) : term27 _133271 v u.
Proof. exact (fun h0 : term26 _133271 v u => @lem7125164 _133271 v u h1 h0). Qed.
Lemma lem7125166 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term26 _133271 v u) : term26 _133271 v u.
Proof. exact (h1). Qed.
Lemma lem7125167 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term24 _133271 v u) (h2 : term26 _133271 v u) : term24 _133271 v u.
Proof. exact (@lem7125165 _133271 v u h1 (@lem7125166 _133271 v u h2)). Qed.
Lemma lem7125168 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term26 _133271 v u) : term26 _133271 v u.
Proof. exact (fun h0 : term24 _133271 v u => @lem7125167 _133271 v u h0 h1). Qed.
Lemma lem7125169 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term28 _133271 v u.
Proof. exact (fun h0 : term26 _133271 v u => @lem7125168 _133271 v u h0). Qed.
Lemma lem7125172 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term26 _133271 v u.
Proof. exact (@lem7125169 _133271 v u (@lem7125161 _133271 v u)). Qed.
Lemma lem7125173 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term26 _133271 v u.
Proof. exact (@lem7125172 _133271 v u). Qed.
Lemma lem7125183 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7125184 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term24 _133271 v u) = (term29 _133271 v u).
Proof. exact (@lem7125183 (term25 _133271 v u)). Qed.
Lemma lem7125186 (t : Prop) : (term30 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7125187 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term29 _133271 v u) = (term22 _133271 v u).
Proof. exact (@lem7125186 (term22 _133271 v u)). Qed.
Lemma lem7125192 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term24 _133271 v u) = (term22 _133271 v u).
Proof. exact (TRANS (@lem7125184 _133271 v u) (@lem7125187 _133271 v u)). Qed.
Lemma lem7125199 {_133271 : Type'} (u : _133271 -> Prop) : (term31 _133271 u) = (term32 _133271 u).
Proof. exact (fun_ext (fun v : _133271 -> Prop => @lem7125192 _133271 v u)). Qed.
Lemma lem7125200 {_133271 : Type'} : (@all (_133271 -> Prop)) = (@all (_133271 -> Prop)).
Proof. exact (eq_refl (@all (_133271 -> Prop))). Qed.
Lemma lem7125201 {_133271 : Type'} (u : _133271 -> Prop) : (term33 _133271 u) = (term34 _133271 u).
Proof. exact (MK_COMB (@lem7125200 _133271) (@lem7125199 _133271 u)). Qed.
Lemma lem7125206 {_133271 : Type'} : (term35 _133271) = (term36 _133271).
Proof. exact (fun_ext (fun u : _133271 -> Prop => @lem7125201 _133271 u)). Qed.
Lemma lem7125207 {_133271 : Type'} : (@all (_133271 -> Prop)) = (@all (_133271 -> Prop)).
Proof. exact (eq_refl (@all (_133271 -> Prop))). Qed.
Lemma lem7125216 {_133271 : Type'} : (term37 _133271) = (term38 _133271).
Proof. exact (MK_COMB (@lem7125207 _133271) (@lem7125206 _133271)). Qed.
Lemma lem7125235 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : ((term7 _133271 u v x) = (term19 _133271 v u x)) = ((term7 _133271 u v x) = (term19 _133271 v u x)).
Proof. exact (eq_refl ((term7 _133271 u v x) = (term19 _133271 v u x))). Qed.
Lemma lem7125236 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term21 _133271 v u) = (term21 _133271 v u).
Proof. exact (fun_ext (fun x : _133271 => @lem7125235 _133271 v u x)). Qed.
Lemma lem7125237 {_133271 : Type'} : (@all _133271) = (@all _133271).
Proof. exact (eq_refl (@all _133271)). Qed.
Lemma lem7125238 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term22 _133271 v u) = (term22 _133271 v u).
Proof. exact (MK_COMB (@lem7125237 _133271) (@lem7125236 _133271 v u)). Qed.
Lemma lem7125239 {_133271 : Type'} (u : _133271 -> Prop) : (term32 _133271 u) = (term32 _133271 u).
Proof. exact (fun_ext (fun v : _133271 -> Prop => @lem7125238 _133271 v u)). Qed.
Lemma lem7125240 {_133271 : Type'} : (@all (_133271 -> Prop)) = (@all (_133271 -> Prop)).
Proof. exact (eq_refl (@all (_133271 -> Prop))). Qed.
Lemma lem7125241 {_133271 : Type'} (u : _133271 -> Prop) : (term34 _133271 u) = (term34 _133271 u).
Proof. exact (MK_COMB (@lem7125240 _133271) (@lem7125239 _133271 u)). Qed.
Lemma lem7125242 {_133271 : Type'} : (term36 _133271) = (term36 _133271).
Proof. exact (fun_ext (fun u : _133271 -> Prop => @lem7125241 _133271 u)). Qed.
Lemma lem7125243 {_133271 : Type'} : (@all (_133271 -> Prop)) = (@all (_133271 -> Prop)).
Proof. exact (eq_refl (@all (_133271 -> Prop))). Qed.
Lemma lem7125244 {_133271 : Type'} : (term38 _133271) = (term38 _133271).
Proof. exact (MK_COMB (@lem7125243 _133271) (@lem7125242 _133271)). Qed.
Lemma lem7125271 {_133271 : Type'} : (term37 _133271) = (term38 _133271).
Proof. exact (TRANS (@lem7125216 _133271) (@lem7125244 _133271)). Qed.
Lemma lem7125272 {_133271 : Type'} : (term38 _133271) = (term37 _133271).
Proof. exact (SYM (@lem7125271 _133271)). Qed.
Lemma lem7125274 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7125275 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : ((term7 _133271 u v x) = (term19 _133271 v u x)) = (term39 _133271 v u x).
Proof. exact (@lem7125274 ((term7 _133271 u v x) = (term19 _133271 v u x))). Qed.
Lemma lem7125276 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term39 _133271 v u x) = ((term7 _133271 u v x) = (term19 _133271 v u x)).
Proof. exact (SYM (@lem7125275 _133271 v u x)). Qed.
Lemma lem7125277 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term40 _133271 v u x) : term40 _133271 v u x.
Proof. exact (h1). Qed.
Lemma lem7125286 {_133271 : Type'} (u : _133271 -> Prop) (v : _133271 -> Prop) (x : _133271) : (term41 _133271 u v x) = (term42 _133271 u v x).
Proof. exact (@lem17160 (u x) (v x)). Qed.
Lemma lem7125297 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term43 _133271 u x) = (u x).
Proof. exact (@lem16933 (u x)). Qed.
Lemma lem7125299 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (term44 _133271 v x) = (term44 _133271 v x).
Proof. exact (eq_refl (term44 _133271 v x)). Qed.
Lemma lem7125300 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term45 _133271 v u x) = (term46 _133271 v u x).
Proof. exact (MK_COMB (@lem7125299 _133271 v x) (@lem7125297 _133271 u x)). Qed.
Lemma lem7125301 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term47 _133271 v u x) = (term45 _133271 v u x).
Proof. exact (@lem17045 (v x) (term17 _133271 u x)). Qed.
Lemma lem7125302 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term47 _133271 v u x) = (term46 _133271 v u x).
Proof. exact (TRANS (@lem7125301 _133271 v u x) (@lem7125300 _133271 v u x)). Qed.
Lemma lem7125307 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term48 _133271 u x) = (term48 _133271 u x).
Proof. exact (eq_refl (term48 _133271 u x)). Qed.
Lemma lem7125308 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term49 _133271 v u x) = (term50 _133271 v u x).
Proof. exact (MK_COMB (@lem7125307 _133271 u x) (@lem7125302 _133271 v u x)). Qed.
Lemma lem7125309 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term51 _133271 v u x) = (term49 _133271 v u x).
Proof. exact (@lem17160 (u x) (term18 _133271 v u x)). Qed.
Lemma lem7125310 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term51 _133271 v u x) = (term50 _133271 v u x).
Proof. exact (TRANS (@lem7125309 _133271 v u x) (@lem7125308 _133271 v u x)). Qed.
Lemma lem7125313 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term19 _133271 v u x) = (term19 _133271 v u x).
Proof. exact (eq_refl (term19 _133271 v u x)). Qed.
Lemma lem7125314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7125315 {_133271 : Type'} (u : _133271 -> Prop) (v : _133271 -> Prop) (x : _133271) : (term52 _133271 u v x) = (term53 _133271 u v x).
Proof. exact (MK_COMB (@lem7125314) (@lem7125286 _133271 u v x)). Qed.
Lemma lem7125316 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term54 _133271 v u x) = (term55 _133271 v u x).
Proof. exact (MK_COMB (@lem7125315 _133271 u v x) (@lem7125313 _133271 v u x)). Qed.
Lemma lem7125318 {_133271 : Type'} (u : _133271 -> Prop) (v : _133271 -> Prop) (x : _133271) : (term56 _133271 u v x) = (term56 _133271 u v x).
Proof. exact (eq_refl (term56 _133271 u v x)). Qed.
Lemma lem7125319 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term57 _133271 v u x) = (term58 _133271 v u x).
Proof. exact (MK_COMB (@lem7125318 _133271 u v x) (@lem7125310 _133271 v u x)). Qed.
Lemma lem7125320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7125321 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term59 _133271 v u x) = (term60 _133271 v u x).
Proof. exact (MK_COMB (@lem7125320) (@lem7125319 _133271 v u x)). Qed.
Lemma lem7125322 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term61 _133271 v u x) = (term62 _133271 v u x).
Proof. exact (MK_COMB (@lem7125321 _133271 v u x) (@lem7125316 _133271 v u x)). Qed.
Lemma lem7125323 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term40 _133271 v u x) = (term61 _133271 v u x).
Proof. exact (@lem17646 (term7 _133271 u v x) (term19 _133271 v u x)). Qed.
Lemma lem7125328 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term40 _133271 v u x) = (term62 _133271 v u x).
Proof. exact (TRANS (@lem7125323 _133271 v u x) (@lem7125322 _133271 v u x)). Qed.
Lemma lem7125397 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term40 _133271 v u x) : term62 _133271 v u x.
Proof. exact (EQ_MP (@lem7125328 _133271 v u x) (@lem7125277 _133271 v u x h1)). Qed.
Lemma lem7125398 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term58 _133271 v u x.
Proof. exact (h1). Qed.
Lemma lem7125399 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : term55 _133271 v u x.
Proof. exact (h1). Qed.
Lemma lem7125400 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term50 _133271 v u x.
Proof. exact (proj2 (@lem7125398 _133271 v u x h1)). Qed.
Lemma lem7125401 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term7 _133271 u v x.
Proof. exact (proj1 (@lem7125398 _133271 v u x h1)). Qed.
Lemma lem7125402 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term46 _133271 v u x.
Proof. exact (proj2 (@lem7125400 _133271 v u x h1)). Qed.
Lemma lem7125410 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : term19 _133271 v u x.
Proof. exact (proj2 (@lem7125399 _133271 v u x h1)). Qed.
Lemma lem7125411 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : term42 _133271 u v x.
Proof. exact (proj1 (@lem7125399 _133271 v u x h1)). Qed.
Lemma lem7125415 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term18 _133271 v u x) : term18 _133271 v u x.
Proof. exact (h1). Qed.
Lemma lem7125429 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125437 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) : term17 _133271 v x.
Proof. exact (h1). Qed.
Lemma lem7125441 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7125449 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125453 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125461 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125477 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125495 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term17 _133271 u x.
Proof. exact (proj1 (@lem7125400 _133271 v u x h1)). Qed.
Lemma lem7125499 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125503 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) : term17 _133271 v x.
Proof. exact (h1). Qed.
Lemma lem7125505 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7125507 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term17 _133271 u x.
Proof. exact (proj1 (@lem7125400 _133271 v u x h1)). Qed.
Lemma lem7125509 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125511 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125513 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term17 _133271 u x.
Proof. exact (proj1 (@lem7125400 _133271 v u x h1)). Qed.
Lemma lem7125515 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125519 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : term17 _133271 u x.
Proof. exact (proj1 (@lem7125411 _133271 v u x h1)). Qed.
Lemma lem7125523 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125527 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : term17 _133271 v x.
Proof. exact (proj2 (@lem7125411 _133271 v u x h1)). Qed.
Lemma lem7125533 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125534 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : term63 _133271 u x.
Proof. exact (fun h0 : term17 _133271 u x => @lem7125533 _133271 u x h1). Qed.
Lemma lem7125536 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125537 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term63 _133271 u x) = (u x).
Proof. exact (@lem7125536 (u x)). Qed.
Lemma lem7125538 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem7125537 _133271 u x) (@lem7125534 _133271 u x h1)). Qed.
Lemma lem7125541 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7125543 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term17 _133271 u x) = (term65 _133271 u x).
Proof. exact (@lem7125541 (u x)). Qed.
Lemma lem7125546 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term65 _133271 u x.
Proof. exact (EQ_MP (@lem7125543 _133271 u x) (@lem7125495 _133271 v u x h1)). Qed.
Lemma lem7125549 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (@lem7125546 _133271 v u x h2 (@lem7125538 _133271 u x h1)). Qed.
Lemma lem7125550 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7125549 _133271 v u x h1 h2). Qed.
Lemma lem7125552 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125553 : term66 = False.
Proof. exact (@lem7125552 False). Qed.
Lemma lem7125554 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125553) (@lem7125550 _133271 v u x h1 h2)). Qed.
Lemma lem7125556 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7125557 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : v x) : term63 _133271 v x.
Proof. exact (fun h0 : term17 _133271 v x => @lem7125556 _133271 v x h1). Qed.
Lemma lem7125559 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125560 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (term63 _133271 v x) = (v x).
Proof. exact (@lem7125559 (v x)). Qed.
Lemma lem7125561 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : v x) : v x.
Proof. exact (EQ_MP (@lem7125560 _133271 v x) (@lem7125557 _133271 v x h1)). Qed.
Lemma lem7125564 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7125566 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (term17 _133271 v x) = (term65 _133271 v x).
Proof. exact (@lem7125564 (v x)). Qed.
Lemma lem7125569 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) : term65 _133271 v x.
Proof. exact (EQ_MP (@lem7125566 _133271 v x) (@lem7125503 _133271 v x h1)). Qed.
Lemma lem7125572 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (@lem7125569 _133271 v x h1 (@lem7125561 _133271 v x h2)). Qed.
Lemma lem7125573 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : term66.
Proof. exact (fun h0 : ~ False => @lem7125572 _133271 v x h1 h2). Qed.
Lemma lem7125575 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125576 : term66 = False.
Proof. exact (@lem7125575 False). Qed.
Lemma lem7125577 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7125576) (@lem7125573 _133271 v x h1 h2)). Qed.
Lemma lem7125579 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125580 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : term63 _133271 u x.
Proof. exact (fun h0 : term17 _133271 u x => @lem7125579 _133271 u x h1). Qed.
Lemma lem7125582 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125583 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term63 _133271 u x) = (u x).
Proof. exact (@lem7125582 (u x)). Qed.
Lemma lem7125584 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem7125583 _133271 u x) (@lem7125580 _133271 u x h1)). Qed.
Lemma lem7125587 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7125589 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term17 _133271 u x) = (term65 _133271 u x).
Proof. exact (@lem7125587 (u x)). Qed.
Lemma lem7125592 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term65 _133271 u x.
Proof. exact (EQ_MP (@lem7125589 _133271 u x) (@lem7125507 _133271 v u x h1)). Qed.
Lemma lem7125595 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (@lem7125592 _133271 v u x h2 (@lem7125584 _133271 u x h1)). Qed.
Lemma lem7125596 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7125595 _133271 v u x h1 h2). Qed.
Lemma lem7125598 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125599 : term66 = False.
Proof. exact (@lem7125598 False). Qed.
Lemma lem7125600 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125599) (@lem7125596 _133271 v u x h1 h2)). Qed.
Lemma lem7125602 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125603 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : term63 _133271 u x.
Proof. exact (fun h0 : term17 _133271 u x => @lem7125602 _133271 u x h1). Qed.
Lemma lem7125605 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125606 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term63 _133271 u x) = (u x).
Proof. exact (@lem7125605 (u x)). Qed.
Lemma lem7125607 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem7125606 _133271 u x) (@lem7125603 _133271 u x h1)). Qed.
Lemma lem7125610 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7125612 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term17 _133271 u x) = (term65 _133271 u x).
Proof. exact (@lem7125610 (u x)). Qed.
Lemma lem7125615 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : term65 _133271 u x.
Proof. exact (EQ_MP (@lem7125612 _133271 u x) (@lem7125513 _133271 v u x h1)). Qed.
Lemma lem7125618 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (@lem7125615 _133271 v u x h2 (@lem7125607 _133271 u x h1)). Qed.
Lemma lem7125619 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7125618 _133271 v u x h1 h2). Qed.
Lemma lem7125621 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125622 : term66 = False.
Proof. exact (@lem7125621 False). Qed.
Lemma lem7125623 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125622) (@lem7125619 _133271 v u x h1 h2)). Qed.
Lemma lem7125625 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7125626 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : term63 _133271 u x.
Proof. exact (fun h0 : term17 _133271 u x => @lem7125625 _133271 u x h1). Qed.
Lemma lem7125628 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125629 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term63 _133271 u x) = (u x).
Proof. exact (@lem7125628 (u x)). Qed.
Lemma lem7125630 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem7125629 _133271 u x) (@lem7125626 _133271 u x h1)). Qed.
Lemma lem7125633 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7125635 {_133271 : Type'} (u : _133271 -> Prop) (x : _133271) : (term17 _133271 u x) = (term65 _133271 u x).
Proof. exact (@lem7125633 (u x)). Qed.
Lemma lem7125638 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : term65 _133271 u x.
Proof. exact (EQ_MP (@lem7125635 _133271 u x) (@lem7125519 _133271 v u x h1)). Qed.
Lemma lem7125641 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : False.
Proof. exact (@lem7125638 _133271 v u x h2 (@lem7125630 _133271 u x h1)). Qed.
Lemma lem7125642 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7125641 _133271 v u x h1 h2). Qed.
Lemma lem7125644 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125645 : term66 = False.
Proof. exact (@lem7125644 False). Qed.
Lemma lem7125646 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125645) (@lem7125642 _133271 v u x h1 h2)). Qed.
Lemma lem7125648 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term18 _133271 v u x) : v x.
Proof. exact (proj1 (@lem7125415 _133271 v u x h1)). Qed.
Lemma lem7125649 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term18 _133271 v u x) : term63 _133271 v x.
Proof. exact (fun h0 : term17 _133271 v x => @lem7125648 _133271 v u x h1). Qed.
Lemma lem7125651 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125652 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (term63 _133271 v x) = (v x).
Proof. exact (@lem7125651 (v x)). Qed.
Lemma lem7125653 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term18 _133271 v u x) : v x.
Proof. exact (EQ_MP (@lem7125652 _133271 v x) (@lem7125649 _133271 v u x h1)). Qed.
Lemma lem7125656 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7125658 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) : (term17 _133271 v x) = (term65 _133271 v x).
Proof. exact (@lem7125656 (v x)). Qed.
Lemma lem7125661 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : term65 _133271 v x.
Proof. exact (EQ_MP (@lem7125658 _133271 v x) (@lem7125527 _133271 v u x h1)). Qed.
Lemma lem7125664 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term18 _133271 v u x) (h2 : term55 _133271 v u x) : False.
Proof. exact (@lem7125661 _133271 v u x h2 (@lem7125653 _133271 v u x h1)). Qed.
Lemma lem7125665 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term18 _133271 v u x) (h2 : term55 _133271 v u x) : term66.
Proof. exact (fun h0 : ~ False => @lem7125664 _133271 v u x h1 h2). Qed.
Lemma lem7125667 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7125668 : term66 = False.
Proof. exact (@lem7125667 False). Qed.
Lemma lem7125669 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term18 _133271 v u x) (h2 : term55 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125668) (@lem7125665 _133271 v u x h1 h2)). Qed.
Lemma lem7125670 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125646 _133271 v u x h1 h2) (fun h3 : False => @lem7125523 _133271 u x h1)). Qed.
Lemma lem7125671 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125670 _133271 v u x h1 h2) (@lem7125523 _133271 u x h1)). Qed.
Lemma lem7125672 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125623 _133271 v u x h1 h2) (fun h3 : False => @lem7125515 _133271 u x h1)). Qed.
Lemma lem7125673 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125672 _133271 v u x h1 h2) (@lem7125515 _133271 u x h1)). Qed.
Lemma lem7125674 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125600 _133271 v u x h1 h2) (fun h3 : False => @lem7125511 _133271 u x h1)). Qed.
Lemma lem7125675 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125674 _133271 v u x h1 h2) (@lem7125511 _133271 u x h1)). Qed.
Lemma lem7125676 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125675 _133271 v u x h1 h2) (fun h3 : False => @lem7125509 _133271 u x h1)). Qed.
Lemma lem7125677 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125676 _133271 v u x h1 h2) (@lem7125509 _133271 u x h1)). Qed.
Lemma lem7125678 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7125577 _133271 v x h1 h2) (fun h3 : False => @lem7125505 _133271 v x h2)). Qed.
Lemma lem7125679 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7125678 _133271 v x h1 h2) (@lem7125505 _133271 v x h2)). Qed.
Lemma lem7125680 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : (term17 _133271 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _133271 v x => @lem7125679 _133271 v x h1 h2) (fun h3 : False => @lem7125503 _133271 v x h1)). Qed.
Lemma lem7125681 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7125680 _133271 v x h1 h2) (@lem7125503 _133271 v x h1)). Qed.
Lemma lem7125682 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125554 _133271 v u x h1 h2) (fun h3 : False => @lem7125499 _133271 u x h1)). Qed.
Lemma lem7125683 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125682 _133271 v u x h1 h2) (@lem7125499 _133271 u x h1)). Qed.
Lemma lem7125684 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125671 _133271 v u x h1 h2) (fun h3 : False => @lem7125477 _133271 u x h1)). Qed.
Lemma lem7125685 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125684 _133271 v u x h1 h2) (@lem7125477 _133271 u x h1)). Qed.
Lemma lem7125686 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125673 _133271 v u x h1 h2) (fun h3 : False => @lem7125461 _133271 u x h1)). Qed.
Lemma lem7125687 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125686 _133271 v u x h1 h2) (@lem7125461 _133271 u x h1)). Qed.
Lemma lem7125688 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125677 _133271 v u x h1 h2) (fun h3 : False => @lem7125453 _133271 u x h1)). Qed.
Lemma lem7125689 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125688 _133271 v u x h1 h2) (@lem7125453 _133271 u x h1)). Qed.
Lemma lem7125690 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125689 _133271 v u x h1 h2) (fun h3 : False => @lem7125449 _133271 u x h1)). Qed.
Lemma lem7125691 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125690 _133271 v u x h1 h2) (@lem7125449 _133271 u x h1)). Qed.
Lemma lem7125692 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7125681 _133271 v x h1 h2) (fun h3 : False => @lem7125441 _133271 v x h2)). Qed.
Lemma lem7125693 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7125692 _133271 v x h1 h2) (@lem7125441 _133271 v x h2)). Qed.
Lemma lem7125694 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : (term17 _133271 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _133271 v x => @lem7125693 _133271 v x h1 h2) (fun h3 : False => @lem7125437 _133271 v x h1)). Qed.
Lemma lem7125695 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7125694 _133271 v x h1 h2) (@lem7125437 _133271 v x h1)). Qed.
Lemma lem7125696 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125683 _133271 v u x h1 h2) (fun h3 : False => @lem7125429 _133271 u x h1)). Qed.
Lemma lem7125697 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125696 _133271 v u x h1 h2) (@lem7125429 _133271 u x h1)). Qed.
Lemma lem7125698 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125685 _133271 v u x h1 h2) (fun h3 : False => @lem7125477 _133271 u x h1)). Qed.
Lemma lem7125699 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term55 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125698 _133271 v u x h1 h2) (@lem7125477 _133271 u x h1)). Qed.
Lemma lem7125700 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125687 _133271 v u x h1 h2) (fun h3 : False => @lem7125461 _133271 u x h1)). Qed.
Lemma lem7125701 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125700 _133271 v u x h1 h2) (@lem7125461 _133271 u x h1)). Qed.
Lemma lem7125702 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125691 _133271 v u x h1 h2) (fun h3 : False => @lem7125453 _133271 u x h1)). Qed.
Lemma lem7125703 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125702 _133271 v u x h1 h2) (@lem7125453 _133271 u x h1)). Qed.
Lemma lem7125704 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125703 _133271 v u x h1 h2) (fun h3 : False => @lem7125449 _133271 u x h1)). Qed.
Lemma lem7125705 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125704 _133271 v u x h1 h2) (@lem7125449 _133271 u x h1)). Qed.
Lemma lem7125706 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7125695 _133271 v x h1 h2) (fun h3 : False => @lem7125441 _133271 v x h2)). Qed.
Lemma lem7125707 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7125706 _133271 v x h1 h2) (@lem7125441 _133271 v x h2)). Qed.
Lemma lem7125708 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : (term17 _133271 v x) = False.
Proof. exact (prop_ext (fun h3 : term17 _133271 v x => @lem7125707 _133271 v x h1 h2) (fun h3 : False => @lem7125437 _133271 v x h1)). Qed.
Lemma lem7125709 {_133271 : Type'} (v : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7125708 _133271 v x h1 h2) (@lem7125437 _133271 v x h1)). Qed.
Lemma lem7125710 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7125697 _133271 v u x h1 h2) (fun h3 : False => @lem7125429 _133271 u x h1)). Qed.
Lemma lem7125711 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125710 _133271 v u x h1 h2) (@lem7125429 _133271 u x h1)). Qed.
Lemma lem7125712 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term55 _133271 v u x) : False.
Proof. exact (or_elim (@lem7125410 _133271 v u x h1) (fun h0 : u x => @lem7125699 _133271 v u x h0 h1) (fun h0 : term18 _133271 v u x => @lem7125669 _133271 v u x h0 h1)). Qed.
Lemma lem7125713 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : u x) (h2 : term58 _133271 v u x) : False.
Proof. exact (or_elim (@lem7125401 _133271 v u x h2) (fun h0 : u x => @lem7125705 _133271 v u x h1 h2) (fun h0 : v x => @lem7125701 _133271 v u x h1 h2)). Qed.
Lemma lem7125714 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term17 _133271 v x) (h2 : term58 _133271 v u x) : False.
Proof. exact (or_elim (@lem7125401 _133271 v u x h2) (fun h0 : u x => @lem7125711 _133271 v u x h0 h2) (fun h0 : v x => @lem7125709 _133271 v x h1 h0)). Qed.
Lemma lem7125715 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term58 _133271 v u x) : False.
Proof. exact (or_elim (@lem7125402 _133271 v u x h1) (fun h0 : term17 _133271 v x => @lem7125714 _133271 v u x h0 h1) (fun h0 : u x => @lem7125713 _133271 v u x h0 h1)). Qed.
Lemma lem7125716 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term40 _133271 v u x) : False.
Proof. exact (or_elim (@lem7125397 _133271 v u x h1) (fun h0 : term58 _133271 v u x => @lem7125715 _133271 v u x h0) (fun h0 : term55 _133271 v u x => @lem7125712 _133271 v u x h0)). Qed.
Lemma lem7125717 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term40 _133271 v u x) : (term40 _133271 v u x) = False.
Proof. exact (prop_ext (fun h2 : term40 _133271 v u x => @lem7125716 _133271 v u x h1) (fun h2 : False => @lem7125277 _133271 v u x h1)). Qed.
Lemma lem7125718 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) (h1 : term40 _133271 v u x) : False.
Proof. exact (EQ_MP (@lem7125717 _133271 v u x h1) (@lem7125277 _133271 v u x h1)). Qed.
Lemma lem7125719 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : term39 _133271 v u x.
Proof. exact (fun h0 : term40 _133271 v u x => @lem7125718 _133271 v u x h0). Qed.
Lemma lem7125720 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (x : _133271) : (term7 _133271 u v x) = (term19 _133271 v u x).
Proof. exact (EQ_MP (@lem7125276 _133271 v u x) (@lem7125719 _133271 v u x)). Qed.
Lemma lem7125725 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term22 _133271 v u.
Proof. exact (fun x : _133271 => @lem7125720 _133271 v u x). Qed.
Lemma lem7125730 {_133271 : Type'} (u : _133271 -> Prop) : term34 _133271 u.
Proof. exact (fun v : _133271 -> Prop => @lem7125725 _133271 v u). Qed.
Lemma lem7125735 {_133271 : Type'} : term38 _133271.
Proof. exact (fun u : _133271 -> Prop => @lem7125730 _133271 u). Qed.
Lemma lem7125736 {_133271 : Type'} : term37 _133271.
Proof. exact (EQ_MP (@lem7125272 _133271) (@lem7125735 _133271)). Qed.
Lemma lem7125737 {_133271 : Type'} (u : _133271 -> Prop) : term67 _133271 u.
Proof. exact (@lem7125736 _133271 u). Qed.
Lemma lem7125738 {_133271 : Type'} (u : _133271 -> Prop) : (term67 _133271 u) = (term33 _133271 u).
Proof. exact (eq_refl (term67 _133271 u)). Qed.
Lemma lem7125739 {_133271 : Type'} (u : _133271 -> Prop) : term33 _133271 u.
Proof. exact (EQ_MP (@lem7125738 _133271 u) (@lem7125737 _133271 u)). Qed.
Lemma lem7125740 {_133271 : Type'} (u : _133271 -> Prop) (v : _133271 -> Prop) : term68 _133271 u v.
Proof. exact (@lem7125739 _133271 u v). Qed.
Lemma lem7125741 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (term68 _133271 u v) = (term24 _133271 v u).
Proof. exact (eq_refl (term68 _133271 u v)). Qed.
Lemma lem7125742 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term24 _133271 v u.
Proof. exact (EQ_MP (@lem7125741 _133271 v u) (@lem7125740 _133271 u v)). Qed.
Lemma lem7125744 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term24 _133271 v u.
Proof. exact (@lem7125173 _133271 v u (@lem7125742 _133271 v u)). Qed.
Lemma lem7125745 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term25 _133271 v u) : False.
Proof. exact (@lem7125744 _133271 v u (@lem7125157 _133271 v u h1)). Qed.
Lemma lem7125746 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term25 _133271 v u) : (term25 _133271 v u) = False.
Proof. exact (prop_ext (fun h2 : term25 _133271 v u => @lem7125745 _133271 v u h1) (fun h2 : False => @lem7125157 _133271 v u h1)). Qed.
Lemma lem7125747 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) (h1 : term25 _133271 v u) : False.
Proof. exact (EQ_MP (@lem7125746 _133271 v u h1) (@lem7125157 _133271 v u h1)). Qed.
Lemma lem7125748 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term24 _133271 v u.
Proof. exact (fun h0 : term25 _133271 v u => @lem7125747 _133271 v u h0). Qed.
Lemma lem7125749 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term22 _133271 v u.
Proof. exact (EQ_MP (@lem7125156 _133271 v u) (@lem7125748 _133271 v u)). Qed.
Lemma lem7125750 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : term2 _133271 v u.
Proof. exact (EQ_MP (@lem7125152 _133271 v u) (@lem7125749 _133271 v u)). Qed.
Lemma lem7125752 (t1 : Prop) : term69 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7125753 (t1 : Prop) : (term69 t1) = (term70 t1).
Proof. exact (eq_refl (term69 t1)). Qed.
Lemma lem7125754 (t1 : Prop) : term70 t1.
Proof. exact (EQ_MP (@lem7125753 t1) (@lem7125752 t1)). Qed.
Lemma lem7125755 (t1 : Prop) (t2 : Prop) : term71 t1 t2.
Proof. exact (@lem7125754 t1 t2). Qed.
Lemma lem7125756 (t1 : Prop) (t2 : Prop) : (term71 t1 t2) = (term72 t1 t2).
Proof. exact (eq_refl (term71 t1 t2)). Qed.
Lemma lem7125757 (t1 : Prop) (t2 : Prop) : term72 t1 t2.
Proof. exact (EQ_MP (@lem7125756 t1 t2) (@lem7125755 t1 t2)). Qed.
Lemma lem7125758 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term73 t1 t2 t3.
Proof. exact (@lem7125757 t1 t2 t3). Qed.
Lemma lem7125759 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term73 t1 t2 t3) = ((term74 t1 t2 t3) = (term75 t1 t2 t3)).
Proof. exact (eq_refl (term73 t1 t2 t3)). Qed.
Lemma lem7125760 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term74 t1 t2 t3) = (term75 t1 t2 t3).
Proof. exact (EQ_MP (@lem7125759 t1 t2 t3) (@lem7125758 t1 t2 t3)). Qed.
Lemma lem7125761 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term75 t1 t2 t3) = (term74 t1 t2 t3).
Proof. exact (SYM (@lem7125760 t1 t2 t3)). Qed.
Lemma lem7125762 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem7125763 {A : Type'} (f : A -> real) (h1 : term76 A) : term77 A f.
Proof. exact (@lem7125762 A h1 f). Qed.
Lemma lem7125764 {A : Type'} (f : A -> real) : (term77 A f) = (term78 A f).
Proof. exact (eq_refl (term77 A f)). Qed.
Lemma lem7125765 {A : Type'} (f : A -> real) (h1 : term76 A) : term78 A f.
Proof. exact (EQ_MP (@lem7125764 A f) (@lem7125763 A f h1)). Qed.
Lemma lem7125766 {A : Type'} (f : A -> real) (u : A -> Prop) (h1 : term76 A) : term79 A f u.
Proof. exact (@lem7125765 A f h1 u). Qed.
Lemma lem7125767 {A : Type'} (u : A -> Prop) (f : A -> real) : (term79 A f u) = (term80 A u f).
Proof. exact (eq_refl (term79 A f u)). Qed.
Lemma lem7125768 {A : Type'} (u : A -> Prop) (f : A -> real) (h1 : term76 A) : term80 A u f.
Proof. exact (EQ_MP (@lem7125767 A u f) (@lem7125766 A f u h1)). Qed.
Lemma lem7125769 {A : Type'} (u : A -> Prop) (f : A -> real) (v : A -> Prop) (h1 : term76 A) : term81 A u f v.
Proof. exact (@lem7125768 A u f h1 v). Qed.
Lemma lem7125770 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term81 A u f v) = (term82 A v u f).
Proof. exact (eq_refl (term81 A u f v)). Qed.
Lemma lem7125771 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term76 A) : term82 A v u f.
Proof. exact (EQ_MP (@lem7125770 A v u f) (@lem7125769 A u f v h1)). Qed.
Lemma lem7125772 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term83 A v u f) : term83 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125773 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term76 A) (h2 : term83 A v u f) : (@sum A v f) = (@sum A u f).
Proof. exact (@lem7125771 A v u f h1 (@lem7125772 A v u f h2)). Qed.
Lemma lem7125774 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term83 A v u f) : term84 A v u f.
Proof. exact (fun h0 : term76 A => @lem7125773 A v u f h0 h1). Qed.
Lemma lem7125775 {A : Type'} (h1 : term76 A) : term76 A.
Proof. exact (h1). Qed.
Lemma lem7125776 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term76 A) (h2 : term83 A v u f) : (@sum A v f) = (@sum A u f).
Proof. exact (@lem7125774 A v u f h2 (@lem7125775 A h1)). Qed.
Lemma lem7125777 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term76 A) : term82 A v u f.
Proof. exact (fun h0 : term83 A v u f => @lem7125776 A v u f h1 h0). Qed.
Lemma lem7125778 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term76 A) : term85 A v u.
Proof. exact (fun f : A -> real => @lem7125777 A v u f h1). Qed.
Lemma lem7125779 {A : Type'} (v : A -> Prop) (h1 : term76 A) : term86 A v.
Proof. exact (fun u : A -> Prop => @lem7125778 A v u h1). Qed.
Lemma lem7125780 {A : Type'} (h1 : term76 A) : term87 A.
Proof. exact (fun v : A -> Prop => @lem7125779 A v h1). Qed.
Lemma lem7125781 {A : Type'} : term88 A.
Proof. exact (fun h0 : term76 A => @lem7125780 A h0). Qed.
Lemma lem7125782 {A : Type'} : term87 A.
Proof. exact (@lem7125781 A (@lem7124972 A)). Qed.
Lemma lem7125783 {A : Type'} (v : A -> Prop) : term89 A v.
Proof. exact (@lem7125782 A v). Qed.
Lemma lem7125784 {A : Type'} (v : A -> Prop) : (term89 A v) = (term86 A v).
Proof. exact (eq_refl (term89 A v)). Qed.
Lemma lem7125785 {A : Type'} (v : A -> Prop) : term86 A v.
Proof. exact (EQ_MP (@lem7125784 A v) (@lem7125783 A v)). Qed.
Lemma lem7125786 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term90 A v u.
Proof. exact (@lem7125785 A v u). Qed.
Lemma lem7125787 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term90 A v u) = (term85 A v u).
Proof. exact (eq_refl (term90 A v u)). Qed.
Lemma lem7125788 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term85 A v u.
Proof. exact (EQ_MP (@lem7125787 A v u) (@lem7125786 A v u)). Qed.
Lemma lem7125789 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term91 A v u f.
Proof. exact (@lem7125788 A v u f). Qed.
Lemma lem7125790 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term91 A v u f) = (term82 A v u f).
Proof. exact (eq_refl (term91 A v u f)). Qed.
Lemma lem7125792 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term92 A v u f) : term92 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125793 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term93 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125794 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : @FINITE A u.
Proof. exact (h1). Qed.
Lemma lem7125798 {_133271 : Type'} (v : _133271 -> Prop) (u : _133271 -> Prop) : (@UNION _133271 u v) = (term1 _133271 v u).
Proof. exact (EQ_MP (@lem7125075 _133271 v u) (@lem7125750 _133271 v u)). Qed.
Lemma lem7125799 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (@UNION A u v) = (term1 A v u).
Proof. exact (@lem7125798 A v u). Qed.
Lemma lem7125800 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7125801 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term94 A u v) = (term95 A v u).
Proof. exact (MK_COMB (@lem7125800 A) (@lem7125799 A v u)). Qed.
Lemma lem7125802 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7125803 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term96 A u v f) = (term97 A v u f).
Proof. exact (MK_COMB (@lem7125801 A v u) (@lem7125802 A f)). Qed.
Lemma lem7125804 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7125805 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term98 A u v f) = (term99 A v u f).
Proof. exact (MK_COMB (@lem7125804) (@lem7125803 A v u f)). Qed.
Lemma lem7125806 {A : Type'} (u : A -> Prop) (f : A -> real) : (@sum A u f) = (@sum A u f).
Proof. exact (eq_refl (@sum A u f)). Qed.
Lemma lem7125807 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term96 A u v f) = (@sum A u f)) = ((term97 A v u f) = (@sum A u f)).
Proof. exact (MK_COMB (@lem7125805 A v u f) (@lem7125806 A u f)). Qed.
Lemma lem7125808 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term97 A v u f) = (@sum A u f)) = ((term96 A u v f) = (@sum A u f)).
Proof. exact (SYM (@lem7125807 A v u f)). Qed.
Lemma lem7125810 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term82 A v u f.
Proof. exact (EQ_MP (@lem7125790 A v u f) (@lem7125789 A v u f)). Qed.
Lemma lem7125811 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term82 A v u f.
Proof. exact (@lem7125810 A v u f). Qed.
Lemma lem7125812 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term100 A v u f.
Proof. exact (@lem7125811 A (term1 A v u) u f). Qed.
Lemma lem7125814 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7125815 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term101 A v u f) = (term102 A v u f).
Proof. exact (@lem7125814 (term101 A v u f)). Qed.
Lemma lem7125816 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term102 A v u f) = (term101 A v u f).
Proof. exact (SYM (@lem7125815 A v u f)). Qed.
Lemma lem7125817 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term103 A v u f) : term103 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125818 {A : Type'} : term104 A.
Proof. exact (@lem3204949 A). Qed.
Lemma lem7125820 {A : Type'} : term105 A.
Proof. exact (@lem3205495 A). Qed.
Lemma lem7125822 {A : Type'} : term106 A.
Proof. exact (@lem3194148 A). Qed.
Lemma lem7125826 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term107 A v u f) : term107 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125827 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term108 A v u f.
Proof. exact (fun h0 : term107 A v u f => @lem7125826 A v u f h0). Qed.
Lemma lem7125828 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term108 A v u f) : term108 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125829 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term107 A v u f) : term107 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125830 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term107 A v u f) (h2 : term108 A v u f) : term107 A v u f.
Proof. exact (@lem7125828 A v u f h2 (@lem7125829 A v u f h1)). Qed.
Lemma lem7125831 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term107 A v u f) : term109 A v u f.
Proof. exact (fun h0 : term108 A v u f => @lem7125830 A v u f h1 h0). Qed.
Lemma lem7125832 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term108 A v u f) : term108 A v u f.
Proof. exact (h1). Qed.
Lemma lem7125833 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term107 A v u f) (h2 : term108 A v u f) : term107 A v u f.
Proof. exact (@lem7125831 A v u f h1 (@lem7125832 A v u f h2)). Qed.
Lemma lem7125834 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term108 A v u f) : term108 A v u f.
Proof. exact (fun h0 : term107 A v u f => @lem7125833 A v u f h0 h1). Qed.
Lemma lem7125835 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term110 A v u f.
Proof. exact (fun h0 : term108 A v u f => @lem7125834 A v u f h0). Qed.
Lemma lem7125838 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term108 A v u f.
Proof. exact (@lem7125835 A v u f (@lem7125827 A v u f)). Qed.
Lemma lem7125839 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term108 A v u f.
Proof. exact (@lem7125838 A v u f). Qed.
Lemma lem7125909 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7125910 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (@lem7125909 (term104 A)). Qed.
Lemma lem7125925 {A : Type'} : (term113 A) = (term113 A).
Proof. exact (eq_refl (term113 A)). Qed.
Lemma lem7125926 {A : Type'} : (term114 A) = (term115 A).
Proof. exact (MK_COMB (@lem7125925 A) (@lem7125910 A)). Qed.
Lemma lem7125929 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (eq_refl (term116 A)). Qed.
Lemma lem7125930 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem7125929 A) (@lem7125926 A)). Qed.
Lemma lem7125933 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term119 A v u f) = (term119 A v u f).
Proof. exact (eq_refl (term119 A v u f)). Qed.
Lemma lem7125934 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term120 A v u f) = (term121 A v u f).
Proof. exact (MK_COMB (@lem7125933 A v u f) (@lem7125930 A)). Qed.
Lemma lem7125937 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term122 A v u f) = (term122 A v u f).
Proof. exact (eq_refl (term122 A v u f)). Qed.
Lemma lem7125938 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term123 A v u f) = (term124 A v u f).
Proof. exact (MK_COMB (@lem7125937 A v u f) (@lem7125934 A v u f)). Qed.
Lemma lem7125941 {A : Type'} (u : A -> Prop) : (term125 A u) = (term125 A u).
Proof. exact (eq_refl (term125 A u)). Qed.
Lemma lem7125942 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term107 A v u f) = (term126 A v u f).
Proof. exact (MK_COMB (@lem7125941 A u) (@lem7125938 A v u f)). Qed.
Lemma lem7125945 {A : Type'} (u : A -> Prop) (f : A -> real) : (term127 A u f) = (term128 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7125942 A v u f)). Qed.
Lemma lem7125946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7125947 {A : Type'} (u : A -> Prop) (f : A -> real) : (term129 A u f) = (term130 A u f).
Proof. exact (MK_COMB (@lem7125946 A) (@lem7125945 A u f)). Qed.
Lemma lem7125952 {A : Type'} (f : A -> real) : (term131 A f) = (term132 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7125947 A u f)). Qed.
Lemma lem7125953 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7125954 {A : Type'} (f : A -> real) : (term133 A f) = (term134 A f).
Proof. exact (MK_COMB (@lem7125953 A) (@lem7125952 A f)). Qed.
Lemma lem7125959 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7125954 A f)). Qed.
Lemma lem7125960 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7125969 {A : Type'} : (term137 A) = (term138 A).
Proof. exact (MK_COMB (@lem7125960 A) (@lem7125959 A)). Qed.
Lemma lem7125978 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term3 A x s t) = (term4 A s x t)) = ((term3 A x s t) = (term4 A s x t)).
Proof. exact (eq_refl ((term3 A x s t) = (term4 A s x t))). Qed.
Lemma lem7125979 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term139 A s t).
Proof. exact (fun_ext (fun x : A => @lem7125978 A s x t)). Qed.
Lemma lem7125980 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7125981 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term140 A s t) = (term140 A s t).
Proof. exact (MK_COMB (@lem7125980 A) (@lem7125979 A s t)). Qed.
Lemma lem7125982 {A : Type'} (s : A -> Prop) : (term141 A s) = (term141 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7125981 A s t)). Qed.
Lemma lem7125983 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7125984 {A : Type'} (s : A -> Prop) : (term142 A s) = (term142 A s).
Proof. exact (MK_COMB (@lem7125983 A) (@lem7125982 A s)). Qed.
Lemma lem7125985 {A : Type'} : (term143 A) = (term143 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7125984 A s)). Qed.
Lemma lem7125986 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7125987 {A : Type'} : (term104 A) = (term104 A).
Proof. exact (MK_COMB (@lem7125986 A) (@lem7125985 A)). Qed.
Lemma lem7125988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7125989 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem7125988) (@lem7125987 A)). Qed.
Lemma lem7126000 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term12 A x s t) = (term13 A s x t)) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl ((term12 A x s t) = (term13 A s x t))). Qed.
Lemma lem7126001 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term144 A s t).
Proof. exact (fun_ext (fun x : A => @lem7126000 A s x t)). Qed.
Lemma lem7126002 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7126003 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term145 A s t) = (term145 A s t).
Proof. exact (MK_COMB (@lem7126002 A) (@lem7126001 A s t)). Qed.
Lemma lem7126004 {A : Type'} (s : A -> Prop) : (term146 A s) = (term146 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126003 A s t)). Qed.
Lemma lem7126005 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126006 {A : Type'} (s : A -> Prop) : (term147 A s) = (term147 A s).
Proof. exact (MK_COMB (@lem7126005 A) (@lem7126004 A s)). Qed.
Lemma lem7126007 {A : Type'} : (term148 A) = (term148 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126006 A s)). Qed.
Lemma lem7126008 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126009 {A : Type'} : (term105 A) = (term105 A).
Proof. exact (MK_COMB (@lem7126008 A) (@lem7126007 A)). Qed.
Lemma lem7126010 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7126011 {A : Type'} : (term113 A) = (term113 A).
Proof. exact (MK_COMB (@lem7126010) (@lem7126009 A)). Qed.
Lemma lem7126012 {A : Type'} : (term115 A) = (term115 A).
Proof. exact (MK_COMB (@lem7126011 A) (@lem7125989 A)). Qed.
Lemma lem7126017 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term149 A s x t) = (term149 A s x t).
Proof. exact (eq_refl (term149 A s x t)). Qed.
Lemma lem7126018 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term150 A s t).
Proof. exact (fun_ext (fun x : A => @lem7126017 A s x t)). Qed.
Lemma lem7126019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7126020 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term151 A s t).
Proof. exact (MK_COMB (@lem7126019 A) (@lem7126018 A s t)). Qed.
Lemma lem7126023 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A s t) = (term152 A s t).
Proof. exact (eq_refl (term152 A s t)). Qed.
Lemma lem7126024 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term151 A s t)) = ((@SUBSET A s t) = (term151 A s t)).
Proof. exact (MK_COMB (@lem7126023 A s t) (@lem7126020 A s t)). Qed.
Lemma lem7126025 {A : Type'} (s : A -> Prop) : (term153 A s) = (term153 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126024 A s t)). Qed.
Lemma lem7126026 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126027 {A : Type'} (s : A -> Prop) : (term154 A s) = (term154 A s).
Proof. exact (MK_COMB (@lem7126026 A) (@lem7126025 A s)). Qed.
Lemma lem7126028 {A : Type'} : (term155 A) = (term155 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126027 A s)). Qed.
Lemma lem7126029 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126030 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem7126029 A) (@lem7126028 A)). Qed.
Lemma lem7126031 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7126032 {A : Type'} : (term116 A) = (term116 A).
Proof. exact (MK_COMB (@lem7126031) (@lem7126030 A)). Qed.
Lemma lem7126033 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (MK_COMB (@lem7126032 A) (@lem7126012 A)). Qed.
Lemma lem7126044 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term156 A v u f x) = (term156 A v u f x).
Proof. exact (eq_refl (term156 A v u f x)). Qed.
Lemma lem7126045 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term157 A v u f) = (term157 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7126044 A v u f x)). Qed.
Lemma lem7126046 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7126047 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term158 A v u f) = (term158 A v u f).
Proof. exact (MK_COMB (@lem7126046 A) (@lem7126045 A v u f)). Qed.
Lemma lem7126050 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term159 A v u) = (term159 A v u).
Proof. exact (eq_refl (term159 A v u)). Qed.
Lemma lem7126051 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term101 A v u f) = (term101 A v u f).
Proof. exact (MK_COMB (@lem7126050 A v u) (@lem7126047 A v u f)). Qed.
Lemma lem7126052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7126053 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term103 A v u f) = (term103 A v u f).
Proof. exact (MK_COMB (@lem7126052) (@lem7126051 A v u f)). Qed.
Lemma lem7126054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7126055 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term119 A v u f) = (term119 A v u f).
Proof. exact (MK_COMB (@lem7126054) (@lem7126053 A v u f)). Qed.
Lemma lem7126056 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term121 A v u f) = (term121 A v u f).
Proof. exact (MK_COMB (@lem7126055 A v u f) (@lem7126033 A)). Qed.
Lemma lem7126067 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term160 A v u f x) = (term160 A v u f x).
Proof. exact (eq_refl (term160 A v u f x)). Qed.
Lemma lem7126068 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term161 A v u f) = (term161 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7126067 A v u f x)). Qed.
Lemma lem7126069 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7126070 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term93 A v u f) = (term93 A v u f).
Proof. exact (MK_COMB (@lem7126069 A) (@lem7126068 A v u f)). Qed.
Lemma lem7126071 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7126072 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term122 A v u f) = (term122 A v u f).
Proof. exact (MK_COMB (@lem7126071) (@lem7126070 A v u f)). Qed.
Lemma lem7126073 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term124 A v u f) = (term124 A v u f).
Proof. exact (MK_COMB (@lem7126072 A v u f) (@lem7126056 A v u f)). Qed.
Lemma lem7126076 {A : Type'} (u : A -> Prop) : (term125 A u) = (term125 A u).
Proof. exact (eq_refl (term125 A u)). Qed.
Lemma lem7126077 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term126 A v u f) = (term126 A v u f).
Proof. exact (MK_COMB (@lem7126076 A u) (@lem7126073 A v u f)). Qed.
Lemma lem7126078 {A : Type'} (u : A -> Prop) (f : A -> real) : (term128 A u f) = (term128 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7126077 A v u f)). Qed.
Lemma lem7126079 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126080 {A : Type'} (u : A -> Prop) (f : A -> real) : (term130 A u f) = (term130 A u f).
Proof. exact (MK_COMB (@lem7126079 A) (@lem7126078 A u f)). Qed.
Lemma lem7126081 {A : Type'} (f : A -> real) : (term132 A f) = (term132 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7126080 A u f)). Qed.
Lemma lem7126082 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126083 {A : Type'} (f : A -> real) : (term134 A f) = (term134 A f).
Proof. exact (MK_COMB (@lem7126082 A) (@lem7126081 A f)). Qed.
Lemma lem7126084 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7126083 A f)). Qed.
Lemma lem7126085 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7126086 {A : Type'} : (term138 A) = (term138 A).
Proof. exact (MK_COMB (@lem7126085 A) (@lem7126084 A)). Qed.
Lemma lem7126199 {A : Type'} : (term137 A) = (term138 A).
Proof. exact (TRANS (@lem7125969 A) (@lem7126086 A)). Qed.
Lemma lem7126200 {A : Type'} : (term138 A) = (term137 A).
Proof. exact (SYM (@lem7126199 A)). Qed.
Lemma lem7126202 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term93 A v u f.
Proof. exact (h1). Qed.
Lemma lem7126203 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term103 A v u f) : term103 A v u f.
Proof. exact (h1). Qed.
Lemma lem7126204 {A : Type'} (h1 : term106 A) : term106 A.
Proof. exact (h1). Qed.
Lemma lem7126205 {A : Type'} (h1 : term105 A) : term105 A.
Proof. exact (h1). Qed.
Lemma lem7126206 {A : Type'} (h1 : term104 A) : term104 A.
Proof. exact (h1). Qed.
Lemma lem7126216 {A : Type'} (x : A) (u : A -> Prop) : (term162 A x u) = (@IN A x u).
Proof. exact (@lem16933 (@IN A x u)). Qed.
Lemma lem7126218 {A : Type'} (x : A) (v : A -> Prop) : (term163 A x v) = (term163 A x v).
Proof. exact (eq_refl (term163 A x v)). Qed.
Lemma lem7126219 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term164 A v x u) = (term165 A v x u).
Proof. exact (MK_COMB (@lem7126218 A x v) (@lem7126216 A x u)). Qed.
Lemma lem7126220 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term166 A v x u) = (term164 A v x u).
Proof. exact (@lem17045 (@IN A x v) (term16 A x u)). Qed.
Lemma lem7126221 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term166 A v x u) = (term165 A v x u).
Proof. exact (TRANS (@lem7126220 A v x u) (@lem7126219 A v x u)). Qed.
Lemma lem7126222 {A : Type'} (f : A -> real) (x : A) : ((f x) = term167) = ((f x) = term167).
Proof. exact (eq_refl ((f x) = term167)). Qed.
Lemma lem7126223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7126224 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term168 A v x u) = (term169 A v x u).
Proof. exact (MK_COMB (@lem7126223) (@lem7126221 A v x u)). Qed.
Lemma lem7126225 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term170 A v u f x) = (term171 A v u f x).
Proof. exact (MK_COMB (@lem7126224 A v x u) (@lem7126222 A f x)). Qed.
Lemma lem7126226 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term160 A v u f x) = (term170 A v u f x).
Proof. exact (@lem17265 (term13 A v x u) ((f x) = term167)). Qed.
Lemma lem7126227 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term160 A v u f x) = (term171 A v u f x).
Proof. exact (TRANS (@lem7126226 A v u f x) (@lem7126225 A v u f x)). Qed.
Lemma lem7126228 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term161 A v u f) = (term172 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7126227 A v u f x)). Qed.
Lemma lem7126229 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7126282 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term93 A v u f) = (term173 A v u f).
Proof. exact (MK_COMB (@lem7126229 A) (@lem7126228 A v u f)). Qed.
Lemma lem7126283 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term173 A v u f.
Proof. exact (EQ_MP (@lem7126282 A v u f) (@lem7126202 A v u f h1)). Qed.
Lemma lem7126295 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term174 A v u f x) = (term175 A v u f x).
Proof. exact (@lem17362 (term176 A v x u) ((f x) = term167)). Qed.
Lemma lem7126296 {A : Type'} (P : A -> Prop) : (term177 A P) = (term178 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7126297 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term179 A v u f) = (term180 A v u f).
Proof. exact (@lem7126296 A (term157 A v u f)). Qed.
Lemma lem7126298 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term181 A v u f x) = (term156 A v u f x).
Proof. exact (eq_refl (term181 A v u f x)). Qed.
Lemma lem7126299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7126300 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term182 A v u f x) = (term174 A v u f x).
Proof. exact (MK_COMB (@lem7126299) (@lem7126298 A v u f x)). Qed.
Lemma lem7126301 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term182 A v u f x) = (term175 A v u f x).
Proof. exact (TRANS (@lem7126300 A v u f x) (@lem7126295 A v u f x)). Qed.
Lemma lem7126302 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term183 A v u f) = (term184 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7126301 A v u f x)). Qed.
Lemma lem7126303 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7126304 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term180 A v u f) = (term185 A v u f).
Proof. exact (MK_COMB (@lem7126303 A) (@lem7126302 A v u f)). Qed.
Lemma lem7126305 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term179 A v u f) = (term185 A v u f).
Proof. exact (TRANS (@lem7126297 A v u f) (@lem7126304 A v u f)). Qed.
Lemma lem7126307 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term186 A v u) = (term186 A v u).
Proof. exact (eq_refl (term186 A v u)). Qed.
Lemma lem7126308 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term187 A v u f) = (term188 A v u f).
Proof. exact (MK_COMB (@lem7126307 A v u) (@lem7126305 A v u f)). Qed.
Lemma lem7126309 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term103 A v u f) = (term187 A v u f).
Proof. exact (@lem17045 (term189 A v u) (term158 A v u f)). Qed.
Lemma lem7126310 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term103 A v u f) = (term188 A v u f).
Proof. exact (TRANS (@lem7126309 A v u f) (@lem7126308 A v u f)). Qed.
Lemma lem7126361 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7126362 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (@lem7126361 A P Q). Qed.
Lemma lem7126363 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term192 A v u f) = (term193 A v u f).
Proof. exact (@lem7126362 A (term194 A v u) (term184 A v u f)). Qed.
Lemma lem7126364 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term195 A v u f x) = (term175 A v u f x).
Proof. exact (eq_refl (term195 A v u f x)). Qed.
Lemma lem7126365 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term196 A v u f) = (term184 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7126364 A v u f x)). Qed.
Lemma lem7126366 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7126367 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term197 A v u f) = (term185 A v u f).
Proof. exact (MK_COMB (@lem7126366 A) (@lem7126365 A v u f)). Qed.
Lemma lem7126368 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term186 A v u) = (term186 A v u).
Proof. exact (eq_refl (term186 A v u)). Qed.
Lemma lem7126369 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term192 A v u f) = (term188 A v u f).
Proof. exact (MK_COMB (@lem7126368 A v u) (@lem7126367 A v u f)). Qed.
Lemma lem7126370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7126371 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term198 A v u f) = (term199 A v u f).
Proof. exact (MK_COMB (@lem7126370) (@lem7126369 A v u f)). Qed.
Lemma lem7126372 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term195 A v u f x) = (term175 A v u f x).
Proof. exact (eq_refl (term195 A v u f x)). Qed.
Lemma lem7126373 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term186 A v u) = (term186 A v u).
Proof. exact (eq_refl (term186 A v u)). Qed.
Lemma lem7126374 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term200 A v u f x) = (term201 A v u f x).
Proof. exact (MK_COMB (@lem7126373 A v u) (@lem7126372 A v u f x)). Qed.
Lemma lem7126375 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term202 A v u f) = (term203 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7126374 A v u f x)). Qed.
Lemma lem7126376 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7126377 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term193 A v u f) = (term204 A v u f).
Proof. exact (MK_COMB (@lem7126376 A) (@lem7126375 A v u f)). Qed.
Lemma lem7126378 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term192 A v u f) = (term193 A v u f)) = ((term188 A v u f) = (term204 A v u f)).
Proof. exact (MK_COMB (@lem7126371 A v u f) (@lem7126377 A v u f)). Qed.
Lemma lem7126380 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term188 A v u f) = (term204 A v u f).
Proof. exact (EQ_MP (@lem7126378 A v u f) (@lem7126363 A v u f)). Qed.
Lemma lem7126381 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term103 A v u f) = (term204 A v u f).
Proof. exact (TRANS (@lem7126310 A v u f) (@lem7126380 A v u f)). Qed.
Lemma lem7126382 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term103 A v u f) : term204 A v u f.
Proof. exact (EQ_MP (@lem7126381 A v u f) (@lem7126203 A v u f h1)). Qed.
Lemma lem7126393 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term205 A s x t) = (term13 A s x t).
Proof. exact (@lem17362 (@IN A x s) (@IN A x t)). Qed.
Lemma lem7126398 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term149 A s x t) = (term165 A s x t).
Proof. exact (@lem17265 (@IN A x s) (@IN A x t)). Qed.
Lemma lem7126399 {A : Type'} (P : A -> Prop) : (term177 A P) = (term178 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7126400 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term206 A s t) = (term207 A s t).
Proof. exact (@lem7126399 A (term150 A s t)). Qed.
Lemma lem7126401 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term208 A s t x) = (term149 A s x t).
Proof. exact (eq_refl (term208 A s t x)). Qed.
Lemma lem7126402 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7126403 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term209 A s t x) = (term205 A s x t).
Proof. exact (MK_COMB (@lem7126402) (@lem7126401 A s x t)). Qed.
Lemma lem7126404 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term209 A s t x) = (term13 A s x t).
Proof. exact (TRANS (@lem7126403 A s x t) (@lem7126393 A s x t)). Qed.
Lemma lem7126405 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term210 A s t) = (term211 A s t).
Proof. exact (fun_ext (fun x : A => @lem7126404 A s x t)). Qed.
Lemma lem7126406 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7126407 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term207 A s t) = (term212 A s t).
Proof. exact (MK_COMB (@lem7126406 A) (@lem7126405 A s t)). Qed.
Lemma lem7126408 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term206 A s t) = (term212 A s t).
Proof. exact (TRANS (@lem7126400 A s t) (@lem7126407 A s t)). Qed.
Lemma lem7126409 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term213 A s t).
Proof. exact (fun_ext (fun x : A => @lem7126398 A s x t)). Qed.
Lemma lem7126410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7126411 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term214 A s t).
Proof. exact (MK_COMB (@lem7126410 A) (@lem7126409 A s t)). Qed.
Lemma lem7126413 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term215 A s t) = (term215 A s t).
Proof. exact (eq_refl (term215 A s t)). Qed.
Lemma lem7126414 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term216 A s t) = (term217 A s t).
Proof. exact (MK_COMB (@lem7126413 A s t) (@lem7126411 A s t)). Qed.
Lemma lem7126416 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term218 A s t).
Proof. exact (eq_refl (term218 A s t)). Qed.
Lemma lem7126417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term219 A s t) = (term220 A s t).
Proof. exact (MK_COMB (@lem7126416 A s t) (@lem7126408 A s t)). Qed.
Lemma lem7126418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126419 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term221 A s t) = (term222 A s t).
Proof. exact (MK_COMB (@lem7126418) (@lem7126417 A s t)). Qed.
Lemma lem7126420 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term223 A s t) = (term224 A s t).
Proof. exact (MK_COMB (@lem7126419 A s t) (@lem7126414 A s t)). Qed.
Lemma lem7126421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term151 A s t)) = (term223 A s t).
Proof. exact (@lem17784 (@SUBSET A s t) (term151 A s t)). Qed.
Lemma lem7126422 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = (term151 A s t)) = (term224 A s t).
Proof. exact (TRANS (@lem7126421 A s t) (@lem7126420 A s t)). Qed.
Lemma lem7126423 {A : Type'} (s : A -> Prop) : (term153 A s) = (term225 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126422 A s t)). Qed.
Lemma lem7126424 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126425 {A : Type'} (s : A -> Prop) : (term154 A s) = (term226 A s).
Proof. exact (MK_COMB (@lem7126424 A) (@lem7126423 A s)). Qed.
Lemma lem7126426 {A : Type'} : (term155 A) = (term227 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126425 A s)). Qed.
Lemma lem7126427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126428 {A : Type'} : (term106 A) = (term228 A).
Proof. exact (MK_COMB (@lem7126427 A) (@lem7126426 A)). Qed.
Lemma lem7126434 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7126435 {A : Type'} (P : type686 A) (Q : type686 A) : (term231 A P Q) = (term232 A P Q).
Proof. exact (@lem7126434 (A -> Prop) P Q). Qed.
Lemma lem7126436 {A : Type'} (s : A -> Prop) : (term233 A s) = (term234 A s).
Proof. exact (@lem7126435 A (term235 A s) (term236 A s)). Qed.
Lemma lem7126437 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term237 A s t) = (term220 A s t).
Proof. exact (eq_refl (term237 A s t)). Qed.
Lemma lem7126438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126439 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term238 A s t) = (term222 A s t).
Proof. exact (MK_COMB (@lem7126438) (@lem7126437 A s t)). Qed.
Lemma lem7126440 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term217 A s t).
Proof. exact (eq_refl (term239 A s t)). Qed.
Lemma lem7126441 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term240 A s t) = (term224 A s t).
Proof. exact (MK_COMB (@lem7126439 A s t) (@lem7126440 A s t)). Qed.
Lemma lem7126442 {A : Type'} (s : A -> Prop) : (term241 A s) = (term225 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126441 A s t)). Qed.
Lemma lem7126443 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126444 {A : Type'} (s : A -> Prop) : (term233 A s) = (term226 A s).
Proof. exact (MK_COMB (@lem7126443 A) (@lem7126442 A s)). Qed.
Lemma lem7126445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7126446 {A : Type'} (s : A -> Prop) : (term242 A s) = (term243 A s).
Proof. exact (MK_COMB (@lem7126445) (@lem7126444 A s)). Qed.
Lemma lem7126447 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term237 A s t) = (term220 A s t).
Proof. exact (eq_refl (term237 A s t)). Qed.
Lemma lem7126448 {A : Type'} (s : A -> Prop) : (term244 A s) = (term235 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126447 A s t)). Qed.
Lemma lem7126449 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126450 {A : Type'} (s : A -> Prop) : (term245 A s) = (term246 A s).
Proof. exact (MK_COMB (@lem7126449 A) (@lem7126448 A s)). Qed.
Lemma lem7126451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126452 {A : Type'} (s : A -> Prop) : (term247 A s) = (term248 A s).
Proof. exact (MK_COMB (@lem7126451) (@lem7126450 A s)). Qed.
Lemma lem7126453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term217 A s t).
Proof. exact (eq_refl (term239 A s t)). Qed.
Lemma lem7126454 {A : Type'} (s : A -> Prop) : (term249 A s) = (term236 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126453 A s t)). Qed.
Lemma lem7126455 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126456 {A : Type'} (s : A -> Prop) : (term250 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem7126455 A) (@lem7126454 A s)). Qed.
Lemma lem7126457 {A : Type'} (s : A -> Prop) : (term234 A s) = (term252 A s).
Proof. exact (MK_COMB (@lem7126452 A s) (@lem7126456 A s)). Qed.
Lemma lem7126458 {A : Type'} (s : A -> Prop) : ((term233 A s) = (term234 A s)) = ((term226 A s) = (term252 A s)).
Proof. exact (MK_COMB (@lem7126446 A s) (@lem7126457 A s)). Qed.
Lemma lem7126459 {A : Type'} (s : A -> Prop) : (term226 A s) = (term252 A s).
Proof. exact (EQ_MP (@lem7126458 A s) (@lem7126436 A s)). Qed.
Lemma lem7126652 {A : Type'} : (term227 A) = (term253 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126459 A s)). Qed.
Lemma lem7126653 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126654 {A : Type'} : (term228 A) = (term254 A).
Proof. exact (MK_COMB (@lem7126653 A) (@lem7126652 A)). Qed.
Lemma lem7126656 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7126657 {A : Type'} (P : type686 A) (Q : type686 A) : (term231 A P Q) = (term232 A P Q).
Proof. exact (@lem7126656 (A -> Prop) P Q). Qed.
Lemma lem7126658 {A : Type'} : (term255 A) = (term256 A).
Proof. exact (@lem7126657 A (term257 A) (term258 A)). Qed.
Lemma lem7126659 {A : Type'} (s : A -> Prop) : (term259 A s) = (term246 A s).
Proof. exact (eq_refl (term259 A s)). Qed.
Lemma lem7126660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126661 {A : Type'} (s : A -> Prop) : (term260 A s) = (term248 A s).
Proof. exact (MK_COMB (@lem7126660) (@lem7126659 A s)). Qed.
Lemma lem7126662 {A : Type'} (s : A -> Prop) : (term261 A s) = (term251 A s).
Proof. exact (eq_refl (term261 A s)). Qed.
Lemma lem7126663 {A : Type'} (s : A -> Prop) : (term262 A s) = (term252 A s).
Proof. exact (MK_COMB (@lem7126661 A s) (@lem7126662 A s)). Qed.
Lemma lem7126664 {A : Type'} : (term263 A) = (term253 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126663 A s)). Qed.
Lemma lem7126665 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126666 {A : Type'} : (term255 A) = (term254 A).
Proof. exact (MK_COMB (@lem7126665 A) (@lem7126664 A)). Qed.
Lemma lem7126667 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7126668 {A : Type'} : (term264 A) = (term265 A).
Proof. exact (MK_COMB (@lem7126667) (@lem7126666 A)). Qed.
Lemma lem7126669 {A : Type'} (s : A -> Prop) : (term259 A s) = (term246 A s).
Proof. exact (eq_refl (term259 A s)). Qed.
Lemma lem7126670 {A : Type'} : (term266 A) = (term257 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126669 A s)). Qed.
Lemma lem7126671 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126672 {A : Type'} : (term267 A) = (term268 A).
Proof. exact (MK_COMB (@lem7126671 A) (@lem7126670 A)). Qed.
Lemma lem7126673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126674 {A : Type'} : (term269 A) = (term270 A).
Proof. exact (MK_COMB (@lem7126673) (@lem7126672 A)). Qed.
Lemma lem7126675 {A : Type'} (s : A -> Prop) : (term261 A s) = (term251 A s).
Proof. exact (eq_refl (term261 A s)). Qed.
Lemma lem7126676 {A : Type'} : (term271 A) = (term258 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126675 A s)). Qed.
Lemma lem7126677 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126678 {A : Type'} : (term272 A) = (term273 A).
Proof. exact (MK_COMB (@lem7126677 A) (@lem7126676 A)). Qed.
Lemma lem7126679 {A : Type'} : (term256 A) = (term274 A).
Proof. exact (MK_COMB (@lem7126674 A) (@lem7126678 A)). Qed.
Lemma lem7126680 {A : Type'} : ((term255 A) = (term256 A)) = ((term254 A) = (term274 A)).
Proof. exact (MK_COMB (@lem7126668 A) (@lem7126679 A)). Qed.
Lemma lem7126681 {A : Type'} : (term254 A) = (term274 A).
Proof. exact (EQ_MP (@lem7126680 A) (@lem7126658 A)). Qed.
Lemma lem7126882 {A : Type'} : (term228 A) = (term274 A).
Proof. exact (TRANS (@lem7126654 A) (@lem7126681 A)). Qed.
Lemma lem7126884 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7126885 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (@lem7126884 A P Q). Qed.
Lemma lem7126886 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term275 A s t) = (term276 A s t).
Proof. exact (@lem7126885 A (@SUBSET A s t) (term211 A s t)). Qed.
Lemma lem7126887 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term277 A s t x) = (term13 A s x t).
Proof. exact (eq_refl (term277 A s t x)). Qed.
Lemma lem7126888 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term278 A s t) = (term211 A s t).
Proof. exact (fun_ext (fun x : A => @lem7126887 A s x t)). Qed.
Lemma lem7126889 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7126890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term279 A s t) = (term212 A s t).
Proof. exact (MK_COMB (@lem7126889 A) (@lem7126888 A s t)). Qed.
Lemma lem7126891 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term218 A s t).
Proof. exact (eq_refl (term218 A s t)). Qed.
Lemma lem7126892 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term275 A s t) = (term220 A s t).
Proof. exact (MK_COMB (@lem7126891 A s t) (@lem7126890 A s t)). Qed.
Lemma lem7126893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7126894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term280 A s t) = (term281 A s t).
Proof. exact (MK_COMB (@lem7126893) (@lem7126892 A s t)). Qed.
Lemma lem7126895 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term277 A s t x) = (term13 A s x t).
Proof. exact (eq_refl (term277 A s t x)). Qed.
Lemma lem7126896 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term218 A s t).
Proof. exact (eq_refl (term218 A s t)). Qed.
Lemma lem7126897 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term282 A s t x) = (term283 A s x t).
Proof. exact (MK_COMB (@lem7126896 A s t) (@lem7126895 A s x t)). Qed.
Lemma lem7126898 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term284 A s t) = (term285 A s t).
Proof. exact (fun_ext (fun x : A => @lem7126897 A s x t)). Qed.
Lemma lem7126899 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7126900 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term276 A s t) = (term286 A s t).
Proof. exact (MK_COMB (@lem7126899 A) (@lem7126898 A s t)). Qed.
Lemma lem7126901 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term275 A s t) = (term276 A s t)) = ((term220 A s t) = (term286 A s t)).
Proof. exact (MK_COMB (@lem7126894 A s t) (@lem7126900 A s t)). Qed.
Lemma lem7126902 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term220 A s t) = (term286 A s t).
Proof. exact (EQ_MP (@lem7126901 A s t) (@lem7126886 A s t)). Qed.
Lemma lem7126903 {A : Type'} (s : A -> Prop) : (term235 A s) = (term287 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126902 A s t)). Qed.
Lemma lem7126904 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126905 {A : Type'} (s : A -> Prop) : (term246 A s) = (term288 A s).
Proof. exact (MK_COMB (@lem7126904 A) (@lem7126903 A s)). Qed.
Lemma lem7126907 {A B : Type'} (P : type1413 A B) : (term289 A B P) = (term290 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7126908 {A : Type'} (P : type672 A) : (term291 A P) = (term292 A P).
Proof. exact (@lem7126907 (A -> Prop) A P). Qed.
Lemma lem7126909 {A : Type'} (s : A -> Prop) : (term293 A s) = (term294 A s).
Proof. exact (@lem7126908 A (term295 A s)). Qed.
Lemma lem7126910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term296 A s t) = (term285 A s t).
Proof. exact (eq_refl (term296 A s t)). Qed.
Lemma lem7126911 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7126912 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term297 A s t x) = (term298 A s t x).
Proof. exact (MK_COMB (@lem7126910 A s t) (@lem7126911 A x)). Qed.
Lemma lem7126913 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term298 A s t x) = (term283 A s x t).
Proof. exact (eq_refl (term298 A s t x)). Qed.
Lemma lem7126914 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term297 A s t x) = (term283 A s x t).
Proof. exact (TRANS (@lem7126912 A s t x) (@lem7126913 A s x t)). Qed.
Lemma lem7126915 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term299 A s t) = (term285 A s t).
Proof. exact (fun_ext (fun x : A => @lem7126914 A s x t)). Qed.
Lemma lem7126916 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7126917 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term300 A s t) = (term286 A s t).
Proof. exact (MK_COMB (@lem7126916 A) (@lem7126915 A s t)). Qed.
Lemma lem7126918 {A : Type'} (s : A -> Prop) : (term301 A s) = (term287 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126917 A s t)). Qed.
Lemma lem7126919 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126920 {A : Type'} (s : A -> Prop) : (term293 A s) = (term288 A s).
Proof. exact (MK_COMB (@lem7126919 A) (@lem7126918 A s)). Qed.
Lemma lem7126921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7126922 {A : Type'} (s : A -> Prop) : (term302 A s) = (term303 A s).
Proof. exact (MK_COMB (@lem7126921) (@lem7126920 A s)). Qed.
Lemma lem7126923 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term296 A s t) = (term285 A s t).
Proof. exact (eq_refl (term296 A s t)). Qed.
Lemma lem7126924 {A : Type'} (x : type684 A) (t : A -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem7126925 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term304 A s x t) = (term305 A s x t).
Proof. exact (MK_COMB (@lem7126923 A s t) (@lem7126924 A x t)). Qed.
Lemma lem7126926 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term305 A s x t) = (term306 A s x t).
Proof. exact (eq_refl (term305 A s x t)). Qed.
Lemma lem7126927 {A : Type'} (s : A -> Prop) (x : type684 A) (t : A -> Prop) : (term304 A s x t) = (term306 A s x t).
Proof. exact (TRANS (@lem7126925 A s x t) (@lem7126926 A s x t)). Qed.
Lemma lem7126928 {A : Type'} (s : A -> Prop) (x : type684 A) : (term307 A s x) = (term308 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7126927 A s x t)). Qed.
Lemma lem7126929 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126930 {A : Type'} (s : A -> Prop) (x : type684 A) : (term309 A s x) = (term310 A s x).
Proof. exact (MK_COMB (@lem7126929 A) (@lem7126928 A s x)). Qed.
Lemma lem7126931 {A : Type'} (s : A -> Prop) : (term311 A s) = (term312 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem7126930 A s x)). Qed.
Lemma lem7126932 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7126933 {A : Type'} (s : A -> Prop) : (term294 A s) = (term313 A s).
Proof. exact (MK_COMB (@lem7126932 A) (@lem7126931 A s)). Qed.
Lemma lem7126934 {A : Type'} (s : A -> Prop) : ((term293 A s) = (term294 A s)) = ((term288 A s) = (term313 A s)).
Proof. exact (MK_COMB (@lem7126922 A s) (@lem7126933 A s)). Qed.
Lemma lem7126935 {A : Type'} (s : A -> Prop) : (term288 A s) = (term313 A s).
Proof. exact (EQ_MP (@lem7126934 A s) (@lem7126909 A s)). Qed.
Lemma lem7126936 {A : Type'} (s : A -> Prop) : (term246 A s) = (term313 A s).
Proof. exact (TRANS (@lem7126905 A s) (@lem7126935 A s)). Qed.
Lemma lem7126937 {A : Type'} : (term257 A) = (term314 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126936 A s)). Qed.
Lemma lem7126938 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126939 {A : Type'} : (term268 A) = (term315 A).
Proof. exact (MK_COMB (@lem7126938 A) (@lem7126937 A)). Qed.
Lemma lem7126941 {A B : Type'} (P : type1413 A B) : (term289 A B P) = (term290 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7126942 {A : Type'} (P : type597 A) : (term316 A P) = (term317 A P).
Proof. exact (@lem7126941 (A -> Prop) (type684 A) P). Qed.
Lemma lem7126943 {A : Type'} : (term318 A) = (term319 A).
Proof. exact (@lem7126942 A (term320 A)). Qed.
Lemma lem7126944 {A : Type'} (s : A -> Prop) : (term321 A s) = (term312 A s).
Proof. exact (eq_refl (term321 A s)). Qed.
Lemma lem7126945 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7126946 {A : Type'} (s : A -> Prop) (x : type684 A) : (term322 A s x) = (term323 A s x).
Proof. exact (MK_COMB (@lem7126944 A s) (@lem7126945 A x)). Qed.
Lemma lem7126947 {A : Type'} (s : A -> Prop) (x : type684 A) : (term323 A s x) = (term310 A s x).
Proof. exact (eq_refl (term323 A s x)). Qed.
Lemma lem7126948 {A : Type'} (s : A -> Prop) (x : type684 A) : (term322 A s x) = (term310 A s x).
Proof. exact (TRANS (@lem7126946 A s x) (@lem7126947 A s x)). Qed.
Lemma lem7126949 {A : Type'} (s : A -> Prop) : (term324 A s) = (term312 A s).
Proof. exact (fun_ext (fun x : type684 A => @lem7126948 A s x)). Qed.
Lemma lem7126950 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7126951 {A : Type'} (s : A -> Prop) : (term325 A s) = (term313 A s).
Proof. exact (MK_COMB (@lem7126950 A) (@lem7126949 A s)). Qed.
Lemma lem7126952 {A : Type'} : (term326 A) = (term314 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126951 A s)). Qed.
Lemma lem7126953 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126954 {A : Type'} : (term318 A) = (term315 A).
Proof. exact (MK_COMB (@lem7126953 A) (@lem7126952 A)). Qed.
Lemma lem7126955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7126956 {A : Type'} : (term327 A) = (term328 A).
Proof. exact (MK_COMB (@lem7126955) (@lem7126954 A)). Qed.
Lemma lem7126957 {A : Type'} (s : A -> Prop) : (term321 A s) = (term312 A s).
Proof. exact (eq_refl (term321 A s)). Qed.
Lemma lem7126958 {A : Type'} (x : type638 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7126959 {A : Type'} (x : type638 A) (s : A -> Prop) : (term329 A x s) = (term330 A x s).
Proof. exact (MK_COMB (@lem7126957 A s) (@lem7126958 A x s)). Qed.
Lemma lem7126960 {A : Type'} (x : type638 A) (s : A -> Prop) : (term330 A x s) = (term331 A x s).
Proof. exact (eq_refl (term330 A x s)). Qed.
Lemma lem7126961 {A : Type'} (x : type638 A) (s : A -> Prop) : (term329 A x s) = (term331 A x s).
Proof. exact (TRANS (@lem7126959 A x s) (@lem7126960 A x s)). Qed.
Lemma lem7126962 {A : Type'} (x : type638 A) : (term332 A x) = (term333 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7126961 A x s)). Qed.
Lemma lem7126963 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7126964 {A : Type'} (x : type638 A) : (term334 A x) = (term335 A x).
Proof. exact (MK_COMB (@lem7126963 A) (@lem7126962 A x)). Qed.
Lemma lem7126965 {A : Type'} : (term336 A) = (term337 A).
Proof. exact (fun_ext (fun x : type638 A => @lem7126964 A x)). Qed.
Lemma lem7126966 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7126967 {A : Type'} : (term319 A) = (term338 A).
Proof. exact (MK_COMB (@lem7126966 A) (@lem7126965 A)). Qed.
Lemma lem7126968 {A : Type'} : ((term318 A) = (term319 A)) = ((term315 A) = (term338 A)).
Proof. exact (MK_COMB (@lem7126956 A) (@lem7126967 A)). Qed.
Lemma lem7126969 {A : Type'} : (term315 A) = (term338 A).
Proof. exact (EQ_MP (@lem7126968 A) (@lem7126943 A)). Qed.
Lemma lem7126970 {A : Type'} : (term268 A) = (term338 A).
Proof. exact (TRANS (@lem7126939 A) (@lem7126969 A)). Qed.
Lemma lem7126971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126972 {A : Type'} : (term270 A) = (term339 A).
Proof. exact (MK_COMB (@lem7126971) (@lem7126970 A)). Qed.
Lemma lem7126973 {A : Type'} : (term273 A) = (term273 A).
Proof. exact (eq_refl (term273 A)). Qed.
Lemma lem7126974 {A : Type'} : (term274 A) = (term340 A).
Proof. exact (MK_COMB (@lem7126972 A) (@lem7126973 A)). Qed.
Lemma lem7126976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term341 A P Q) = (term342 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7126977 {A : Type'} (P : type139 A) (Q : Prop) : (term343 A P Q) = (term344 A P Q).
Proof. exact (@lem7126976 (type638 A) P Q). Qed.
Lemma lem7126978 {A : Type'} : (term345 A) = (term346 A).
Proof. exact (@lem7126977 A (term337 A) (term273 A)). Qed.
Lemma lem7126979 {A : Type'} (x : type638 A) : (term347 A x) = (term335 A x).
Proof. exact (eq_refl (term347 A x)). Qed.
Lemma lem7126980 {A : Type'} : (term348 A) = (term337 A).
Proof. exact (fun_ext (fun x : type638 A => @lem7126979 A x)). Qed.
Lemma lem7126981 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7126982 {A : Type'} : (term349 A) = (term338 A).
Proof. exact (MK_COMB (@lem7126981 A) (@lem7126980 A)). Qed.
Lemma lem7126983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126984 {A : Type'} : (term350 A) = (term339 A).
Proof. exact (MK_COMB (@lem7126983) (@lem7126982 A)). Qed.
Lemma lem7126985 {A : Type'} : (term273 A) = (term273 A).
Proof. exact (eq_refl (term273 A)). Qed.
Lemma lem7126986 {A : Type'} : (term345 A) = (term340 A).
Proof. exact (MK_COMB (@lem7126984 A) (@lem7126985 A)). Qed.
Lemma lem7126987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7126988 {A : Type'} : (term351 A) = (term352 A).
Proof. exact (MK_COMB (@lem7126987) (@lem7126986 A)). Qed.
Lemma lem7126989 {A : Type'} (x : type638 A) : (term347 A x) = (term335 A x).
Proof. exact (eq_refl (term347 A x)). Qed.
Lemma lem7126990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7126991 {A : Type'} (x : type638 A) : (term353 A x) = (term354 A x).
Proof. exact (MK_COMB (@lem7126990) (@lem7126989 A x)). Qed.
Lemma lem7126992 {A : Type'} : (term273 A) = (term273 A).
Proof. exact (eq_refl (term273 A)). Qed.
Lemma lem7126993 {A : Type'} (x : type638 A) : (term355 A x) = (term356 A x).
Proof. exact (MK_COMB (@lem7126991 A x) (@lem7126992 A)). Qed.
Lemma lem7126994 {A : Type'} : (term357 A) = (term358 A).
Proof. exact (fun_ext (fun x : type638 A => @lem7126993 A x)). Qed.
Lemma lem7126995 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7126996 {A : Type'} : (term346 A) = (term359 A).
Proof. exact (MK_COMB (@lem7126995 A) (@lem7126994 A)). Qed.
Lemma lem7126997 {A : Type'} : ((term345 A) = (term346 A)) = ((term340 A) = (term359 A)).
Proof. exact (MK_COMB (@lem7126988 A) (@lem7126996 A)). Qed.
Lemma lem7126998 {A : Type'} : (term340 A) = (term359 A).
Proof. exact (EQ_MP (@lem7126997 A) (@lem7126978 A)). Qed.
Lemma lem7126999 {A : Type'} : (term274 A) = (term359 A).
Proof. exact (TRANS (@lem7126974 A) (@lem7126998 A)). Qed.
Lemma lem7127000 {A : Type'} : (term228 A) = (term359 A).
Proof. exact (TRANS (@lem7126882 A) (@lem7126999 A)). Qed.
Lemma lem7127001 {A : Type'} : (term106 A) = (term359 A).
Proof. exact (TRANS (@lem7126428 A) (@lem7127000 A)). Qed.
Lemma lem7127002 {A : Type'} (h1 : term106 A) : term359 A.
Proof. exact (EQ_MP (@lem7127001 A) (@lem7126204 A h1)). Qed.
Lemma lem7127010 {A : Type'} (x : A) (t : A -> Prop) : (term162 A x t) = (@IN A x t).
Proof. exact (@lem16933 (@IN A x t)). Qed.
Lemma lem7127012 {A : Type'} (x : A) (s : A -> Prop) : (term163 A x s) = (term163 A x s).
Proof. exact (eq_refl (term163 A x s)). Qed.
Lemma lem7127013 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term164 A s x t) = (term165 A s x t).
Proof. exact (MK_COMB (@lem7127012 A x s) (@lem7127010 A x t)). Qed.
Lemma lem7127014 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A s x t) = (term164 A s x t).
Proof. exact (@lem17045 (@IN A x s) (term16 A x t)). Qed.
Lemma lem7127015 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term166 A s x t) = (term165 A s x t).
Proof. exact (TRANS (@lem7127014 A s x t) (@lem7127013 A s x t)). Qed.
Lemma lem7127021 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term360 A s x t) = (term360 A s x t).
Proof. exact (eq_refl (term360 A s x t)). Qed.
Lemma lem7127023 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term361 A x s t) = (term361 A x s t).
Proof. exact (eq_refl (term361 A x s t)). Qed.
Lemma lem7127024 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term362 A s x t) = (term363 A s x t).
Proof. exact (MK_COMB (@lem7127023 A x s t) (@lem7127015 A s x t)). Qed.
Lemma lem7127025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127026 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term364 A s x t) = (term365 A s x t).
Proof. exact (MK_COMB (@lem7127025) (@lem7127024 A s x t)). Qed.
Lemma lem7127027 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term366 A s x t) = (term367 A s x t).
Proof. exact (MK_COMB (@lem7127026 A s x t) (@lem7127021 A s x t)). Qed.
Lemma lem7127028 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term12 A x s t) = (term13 A s x t)) = (term366 A s x t).
Proof. exact (@lem17784 (term12 A x s t) (term13 A s x t)). Qed.
Lemma lem7127029 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term12 A x s t) = (term13 A s x t)) = (term367 A s x t).
Proof. exact (TRANS (@lem7127028 A s x t) (@lem7127027 A s x t)). Qed.
Lemma lem7127030 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term368 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127029 A s x t)). Qed.
Lemma lem7127031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127032 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term145 A s t) = (term369 A s t).
Proof. exact (MK_COMB (@lem7127031 A) (@lem7127030 A s t)). Qed.
Lemma lem7127033 {A : Type'} (s : A -> Prop) : (term146 A s) = (term370 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127032 A s t)). Qed.
Lemma lem7127034 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127035 {A : Type'} (s : A -> Prop) : (term147 A s) = (term371 A s).
Proof. exact (MK_COMB (@lem7127034 A) (@lem7127033 A s)). Qed.
Lemma lem7127036 {A : Type'} : (term148 A) = (term372 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127035 A s)). Qed.
Lemma lem7127037 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127038 {A : Type'} : (term105 A) = (term373 A).
Proof. exact (MK_COMB (@lem7127037 A) (@lem7127036 A)). Qed.
Lemma lem7127048 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7127049 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (@lem7127048 A P Q). Qed.
Lemma lem7127050 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term374 A s t) = (term375 A s t).
Proof. exact (@lem7127049 A (term376 A s t) (term377 A s t)). Qed.
Lemma lem7127051 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term378 A s t x) = (term363 A s x t).
Proof. exact (eq_refl (term378 A s t x)). Qed.
Lemma lem7127052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127053 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term379 A s t x) = (term365 A s x t).
Proof. exact (MK_COMB (@lem7127052) (@lem7127051 A s x t)). Qed.
Lemma lem7127054 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term380 A s t x) = (term360 A s x t).
Proof. exact (eq_refl (term380 A s t x)). Qed.
Lemma lem7127055 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term381 A s t x) = (term367 A s x t).
Proof. exact (MK_COMB (@lem7127053 A s x t) (@lem7127054 A s x t)). Qed.
Lemma lem7127056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term382 A s t) = (term368 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127055 A s x t)). Qed.
Lemma lem7127057 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127058 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term374 A s t) = (term369 A s t).
Proof. exact (MK_COMB (@lem7127057 A) (@lem7127056 A s t)). Qed.
Lemma lem7127059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7127060 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term383 A s t) = (term384 A s t).
Proof. exact (MK_COMB (@lem7127059) (@lem7127058 A s t)). Qed.
Lemma lem7127061 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term378 A s t x) = (term363 A s x t).
Proof. exact (eq_refl (term378 A s t x)). Qed.
Lemma lem7127062 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term385 A s t) = (term376 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127061 A s x t)). Qed.
Lemma lem7127063 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term386 A s t) = (term387 A s t).
Proof. exact (MK_COMB (@lem7127063 A) (@lem7127062 A s t)). Qed.
Lemma lem7127065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term388 A s t) = (term389 A s t).
Proof. exact (MK_COMB (@lem7127065) (@lem7127064 A s t)). Qed.
Lemma lem7127067 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term380 A s t x) = (term360 A s x t).
Proof. exact (eq_refl (term380 A s t x)). Qed.
Lemma lem7127068 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term390 A s t) = (term377 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127067 A s x t)). Qed.
Lemma lem7127069 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127070 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term391 A s t) = (term392 A s t).
Proof. exact (MK_COMB (@lem7127069 A) (@lem7127068 A s t)). Qed.
Lemma lem7127071 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term375 A s t) = (term393 A s t).
Proof. exact (MK_COMB (@lem7127066 A s t) (@lem7127070 A s t)). Qed.
Lemma lem7127072 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term374 A s t) = (term375 A s t)) = ((term369 A s t) = (term393 A s t)).
Proof. exact (MK_COMB (@lem7127060 A s t) (@lem7127071 A s t)). Qed.
Lemma lem7127073 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term369 A s t) = (term393 A s t).
Proof. exact (EQ_MP (@lem7127072 A s t) (@lem7127050 A s t)). Qed.
Lemma lem7127170 {A : Type'} (s : A -> Prop) : (term370 A s) = (term394 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127073 A s t)). Qed.
Lemma lem7127171 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127172 {A : Type'} (s : A -> Prop) : (term371 A s) = (term395 A s).
Proof. exact (MK_COMB (@lem7127171 A) (@lem7127170 A s)). Qed.
Lemma lem7127174 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7127175 {A : Type'} (P : type686 A) (Q : type686 A) : (term231 A P Q) = (term232 A P Q).
Proof. exact (@lem7127174 (A -> Prop) P Q). Qed.
Lemma lem7127176 {A : Type'} (s : A -> Prop) : (term396 A s) = (term397 A s).
Proof. exact (@lem7127175 A (term398 A s) (term399 A s)). Qed.
Lemma lem7127177 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term400 A s t) = (term387 A s t).
Proof. exact (eq_refl (term400 A s t)). Qed.
Lemma lem7127178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127179 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term401 A s t) = (term389 A s t).
Proof. exact (MK_COMB (@lem7127178) (@lem7127177 A s t)). Qed.
Lemma lem7127180 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term402 A s t) = (term392 A s t).
Proof. exact (eq_refl (term402 A s t)). Qed.
Lemma lem7127181 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term403 A s t) = (term393 A s t).
Proof. exact (MK_COMB (@lem7127179 A s t) (@lem7127180 A s t)). Qed.
Lemma lem7127182 {A : Type'} (s : A -> Prop) : (term404 A s) = (term394 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127181 A s t)). Qed.
Lemma lem7127183 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127184 {A : Type'} (s : A -> Prop) : (term396 A s) = (term395 A s).
Proof. exact (MK_COMB (@lem7127183 A) (@lem7127182 A s)). Qed.
Lemma lem7127185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7127186 {A : Type'} (s : A -> Prop) : (term405 A s) = (term406 A s).
Proof. exact (MK_COMB (@lem7127185) (@lem7127184 A s)). Qed.
Lemma lem7127187 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term400 A s t) = (term387 A s t).
Proof. exact (eq_refl (term400 A s t)). Qed.
Lemma lem7127188 {A : Type'} (s : A -> Prop) : (term407 A s) = (term398 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127187 A s t)). Qed.
Lemma lem7127189 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127190 {A : Type'} (s : A -> Prop) : (term408 A s) = (term409 A s).
Proof. exact (MK_COMB (@lem7127189 A) (@lem7127188 A s)). Qed.
Lemma lem7127191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127192 {A : Type'} (s : A -> Prop) : (term410 A s) = (term411 A s).
Proof. exact (MK_COMB (@lem7127191) (@lem7127190 A s)). Qed.
Lemma lem7127193 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term402 A s t) = (term392 A s t).
Proof. exact (eq_refl (term402 A s t)). Qed.
Lemma lem7127194 {A : Type'} (s : A -> Prop) : (term412 A s) = (term399 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127193 A s t)). Qed.
Lemma lem7127195 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127196 {A : Type'} (s : A -> Prop) : (term413 A s) = (term414 A s).
Proof. exact (MK_COMB (@lem7127195 A) (@lem7127194 A s)). Qed.
Lemma lem7127197 {A : Type'} (s : A -> Prop) : (term397 A s) = (term415 A s).
Proof. exact (MK_COMB (@lem7127192 A s) (@lem7127196 A s)). Qed.
Lemma lem7127198 {A : Type'} (s : A -> Prop) : ((term396 A s) = (term397 A s)) = ((term395 A s) = (term415 A s)).
Proof. exact (MK_COMB (@lem7127186 A s) (@lem7127197 A s)). Qed.
Lemma lem7127199 {A : Type'} (s : A -> Prop) : (term395 A s) = (term415 A s).
Proof. exact (EQ_MP (@lem7127198 A s) (@lem7127176 A s)). Qed.
Lemma lem7127304 {A : Type'} (s : A -> Prop) : (term371 A s) = (term415 A s).
Proof. exact (TRANS (@lem7127172 A s) (@lem7127199 A s)). Qed.
Lemma lem7127305 {A : Type'} : (term372 A) = (term416 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127304 A s)). Qed.
Lemma lem7127306 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127307 {A : Type'} : (term373 A) = (term417 A).
Proof. exact (MK_COMB (@lem7127306 A) (@lem7127305 A)). Qed.
Lemma lem7127309 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7127310 {A : Type'} (P : type686 A) (Q : type686 A) : (term231 A P Q) = (term232 A P Q).
Proof. exact (@lem7127309 (A -> Prop) P Q). Qed.
Lemma lem7127311 {A : Type'} : (term418 A) = (term419 A).
Proof. exact (@lem7127310 A (term420 A) (term421 A)). Qed.
Lemma lem7127312 {A : Type'} (s : A -> Prop) : (term422 A s) = (term409 A s).
Proof. exact (eq_refl (term422 A s)). Qed.
Lemma lem7127313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127314 {A : Type'} (s : A -> Prop) : (term423 A s) = (term411 A s).
Proof. exact (MK_COMB (@lem7127313) (@lem7127312 A s)). Qed.
Lemma lem7127315 {A : Type'} (s : A -> Prop) : (term424 A s) = (term414 A s).
Proof. exact (eq_refl (term424 A s)). Qed.
Lemma lem7127316 {A : Type'} (s : A -> Prop) : (term425 A s) = (term415 A s).
Proof. exact (MK_COMB (@lem7127314 A s) (@lem7127315 A s)). Qed.
Lemma lem7127317 {A : Type'} : (term426 A) = (term416 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127316 A s)). Qed.
Lemma lem7127318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127319 {A : Type'} : (term418 A) = (term417 A).
Proof. exact (MK_COMB (@lem7127318 A) (@lem7127317 A)). Qed.
Lemma lem7127320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7127321 {A : Type'} : (term427 A) = (term428 A).
Proof. exact (MK_COMB (@lem7127320) (@lem7127319 A)). Qed.
Lemma lem7127322 {A : Type'} (s : A -> Prop) : (term422 A s) = (term409 A s).
Proof. exact (eq_refl (term422 A s)). Qed.
Lemma lem7127323 {A : Type'} : (term429 A) = (term420 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127322 A s)). Qed.
Lemma lem7127324 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127325 {A : Type'} : (term430 A) = (term431 A).
Proof. exact (MK_COMB (@lem7127324 A) (@lem7127323 A)). Qed.
Lemma lem7127326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127327 {A : Type'} : (term432 A) = (term433 A).
Proof. exact (MK_COMB (@lem7127326) (@lem7127325 A)). Qed.
Lemma lem7127328 {A : Type'} (s : A -> Prop) : (term424 A s) = (term414 A s).
Proof. exact (eq_refl (term424 A s)). Qed.
Lemma lem7127329 {A : Type'} : (term434 A) = (term421 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127328 A s)). Qed.
Lemma lem7127330 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127331 {A : Type'} : (term435 A) = (term436 A).
Proof. exact (MK_COMB (@lem7127330 A) (@lem7127329 A)). Qed.
Lemma lem7127332 {A : Type'} : (term419 A) = (term437 A).
Proof. exact (MK_COMB (@lem7127327 A) (@lem7127331 A)). Qed.
Lemma lem7127333 {A : Type'} : ((term418 A) = (term419 A)) = ((term417 A) = (term437 A)).
Proof. exact (MK_COMB (@lem7127321 A) (@lem7127332 A)). Qed.
Lemma lem7127334 {A : Type'} : (term417 A) = (term437 A).
Proof. exact (EQ_MP (@lem7127333 A) (@lem7127311 A)). Qed.
Lemma lem7127449 {A : Type'} : (term373 A) = (term437 A).
Proof. exact (TRANS (@lem7127307 A) (@lem7127334 A)). Qed.
Lemma lem7127450 {A : Type'} : (term105 A) = (term437 A).
Proof. exact (TRANS (@lem7127038 A) (@lem7127449 A)). Qed.
Lemma lem7127451 {A : Type'} (h1 : term105 A) : term437 A.
Proof. exact (EQ_MP (@lem7127450 A) (@lem7126205 A h1)). Qed.
Lemma lem7127462 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term438 A s x t) = (term439 A s x t).
Proof. exact (@lem17160 (@IN A x s) (@IN A x t)). Qed.
Lemma lem7127468 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term440 A s x t) = (term440 A s x t).
Proof. exact (eq_refl (term440 A s x t)). Qed.
Lemma lem7127470 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term441 A x s t) = (term441 A x s t).
Proof. exact (eq_refl (term441 A x s t)). Qed.
Lemma lem7127471 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term442 A s x t) = (term443 A s x t).
Proof. exact (MK_COMB (@lem7127470 A x s t) (@lem7127462 A s x t)). Qed.
Lemma lem7127472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127473 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term444 A s x t) = (term445 A s x t).
Proof. exact (MK_COMB (@lem7127472) (@lem7127471 A s x t)). Qed.
Lemma lem7127474 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term446 A s x t) = (term447 A s x t).
Proof. exact (MK_COMB (@lem7127473 A s x t) (@lem7127468 A s x t)). Qed.
Lemma lem7127475 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term3 A x s t) = (term4 A s x t)) = (term446 A s x t).
Proof. exact (@lem17784 (term3 A x s t) (term4 A s x t)). Qed.
Lemma lem7127476 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term3 A x s t) = (term4 A s x t)) = (term447 A s x t).
Proof. exact (TRANS (@lem7127475 A s x t) (@lem7127474 A s x t)). Qed.
Lemma lem7127477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term448 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127476 A s x t)). Qed.
Lemma lem7127478 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127479 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term140 A s t) = (term449 A s t).
Proof. exact (MK_COMB (@lem7127478 A) (@lem7127477 A s t)). Qed.
Lemma lem7127480 {A : Type'} (s : A -> Prop) : (term141 A s) = (term450 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127479 A s t)). Qed.
Lemma lem7127481 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127482 {A : Type'} (s : A -> Prop) : (term142 A s) = (term451 A s).
Proof. exact (MK_COMB (@lem7127481 A) (@lem7127480 A s)). Qed.
Lemma lem7127483 {A : Type'} : (term143 A) = (term452 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127482 A s)). Qed.
Lemma lem7127484 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127485 {A : Type'} : (term104 A) = (term453 A).
Proof. exact (MK_COMB (@lem7127484 A) (@lem7127483 A)). Qed.
Lemma lem7127495 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7127496 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (@lem7127495 A P Q). Qed.
Lemma lem7127497 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term454 A s t) = (term455 A s t).
Proof. exact (@lem7127496 A (term456 A s t) (term457 A s t)). Qed.
Lemma lem7127498 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term458 A s t x) = (term443 A s x t).
Proof. exact (eq_refl (term458 A s t x)). Qed.
Lemma lem7127499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127500 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term459 A s t x) = (term445 A s x t).
Proof. exact (MK_COMB (@lem7127499) (@lem7127498 A s x t)). Qed.
Lemma lem7127501 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term460 A s t x) = (term440 A s x t).
Proof. exact (eq_refl (term460 A s t x)). Qed.
Lemma lem7127502 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term461 A s t x) = (term447 A s x t).
Proof. exact (MK_COMB (@lem7127500 A s x t) (@lem7127501 A s x t)). Qed.
Lemma lem7127503 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term462 A s t) = (term448 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127502 A s x t)). Qed.
Lemma lem7127504 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127505 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term454 A s t) = (term449 A s t).
Proof. exact (MK_COMB (@lem7127504 A) (@lem7127503 A s t)). Qed.
Lemma lem7127506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7127507 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term463 A s t) = (term464 A s t).
Proof. exact (MK_COMB (@lem7127506) (@lem7127505 A s t)). Qed.
Lemma lem7127508 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term458 A s t x) = (term443 A s x t).
Proof. exact (eq_refl (term458 A s t x)). Qed.
Lemma lem7127509 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term465 A s t) = (term456 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127508 A s x t)). Qed.
Lemma lem7127510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127511 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term466 A s t) = (term467 A s t).
Proof. exact (MK_COMB (@lem7127510 A) (@lem7127509 A s t)). Qed.
Lemma lem7127512 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127513 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term468 A s t) = (term469 A s t).
Proof. exact (MK_COMB (@lem7127512) (@lem7127511 A s t)). Qed.
Lemma lem7127514 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term460 A s t x) = (term440 A s x t).
Proof. exact (eq_refl (term460 A s t x)). Qed.
Lemma lem7127515 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term470 A s t) = (term457 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127514 A s x t)). Qed.
Lemma lem7127516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127517 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term471 A s t) = (term472 A s t).
Proof. exact (MK_COMB (@lem7127516 A) (@lem7127515 A s t)). Qed.
Lemma lem7127518 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term455 A s t) = (term473 A s t).
Proof. exact (MK_COMB (@lem7127513 A s t) (@lem7127517 A s t)). Qed.
Lemma lem7127519 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term454 A s t) = (term455 A s t)) = ((term449 A s t) = (term473 A s t)).
Proof. exact (MK_COMB (@lem7127507 A s t) (@lem7127518 A s t)). Qed.
Lemma lem7127520 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term449 A s t) = (term473 A s t).
Proof. exact (EQ_MP (@lem7127519 A s t) (@lem7127497 A s t)). Qed.
Lemma lem7127617 {A : Type'} (s : A -> Prop) : (term450 A s) = (term474 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127520 A s t)). Qed.
Lemma lem7127618 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127619 {A : Type'} (s : A -> Prop) : (term451 A s) = (term475 A s).
Proof. exact (MK_COMB (@lem7127618 A) (@lem7127617 A s)). Qed.
Lemma lem7127621 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7127622 {A : Type'} (P : type686 A) (Q : type686 A) : (term231 A P Q) = (term232 A P Q).
Proof. exact (@lem7127621 (A -> Prop) P Q). Qed.
Lemma lem7127623 {A : Type'} (s : A -> Prop) : (term476 A s) = (term477 A s).
Proof. exact (@lem7127622 A (term478 A s) (term479 A s)). Qed.
Lemma lem7127624 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term480 A s t) = (term467 A s t).
Proof. exact (eq_refl (term480 A s t)). Qed.
Lemma lem7127625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127626 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term481 A s t) = (term469 A s t).
Proof. exact (MK_COMB (@lem7127625) (@lem7127624 A s t)). Qed.
Lemma lem7127627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term482 A s t) = (term472 A s t).
Proof. exact (eq_refl (term482 A s t)). Qed.
Lemma lem7127628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term483 A s t) = (term473 A s t).
Proof. exact (MK_COMB (@lem7127626 A s t) (@lem7127627 A s t)). Qed.
Lemma lem7127629 {A : Type'} (s : A -> Prop) : (term484 A s) = (term474 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127628 A s t)). Qed.
Lemma lem7127630 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127631 {A : Type'} (s : A -> Prop) : (term476 A s) = (term475 A s).
Proof. exact (MK_COMB (@lem7127630 A) (@lem7127629 A s)). Qed.
Lemma lem7127632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7127633 {A : Type'} (s : A -> Prop) : (term485 A s) = (term486 A s).
Proof. exact (MK_COMB (@lem7127632) (@lem7127631 A s)). Qed.
Lemma lem7127634 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term480 A s t) = (term467 A s t).
Proof. exact (eq_refl (term480 A s t)). Qed.
Lemma lem7127635 {A : Type'} (s : A -> Prop) : (term487 A s) = (term478 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127634 A s t)). Qed.
Lemma lem7127636 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127637 {A : Type'} (s : A -> Prop) : (term488 A s) = (term489 A s).
Proof. exact (MK_COMB (@lem7127636 A) (@lem7127635 A s)). Qed.
Lemma lem7127638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127639 {A : Type'} (s : A -> Prop) : (term490 A s) = (term491 A s).
Proof. exact (MK_COMB (@lem7127638) (@lem7127637 A s)). Qed.
Lemma lem7127640 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term482 A s t) = (term472 A s t).
Proof. exact (eq_refl (term482 A s t)). Qed.
Lemma lem7127641 {A : Type'} (s : A -> Prop) : (term492 A s) = (term479 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127640 A s t)). Qed.
Lemma lem7127642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127643 {A : Type'} (s : A -> Prop) : (term493 A s) = (term494 A s).
Proof. exact (MK_COMB (@lem7127642 A) (@lem7127641 A s)). Qed.
Lemma lem7127644 {A : Type'} (s : A -> Prop) : (term477 A s) = (term495 A s).
Proof. exact (MK_COMB (@lem7127639 A s) (@lem7127643 A s)). Qed.
Lemma lem7127645 {A : Type'} (s : A -> Prop) : ((term476 A s) = (term477 A s)) = ((term475 A s) = (term495 A s)).
Proof. exact (MK_COMB (@lem7127633 A s) (@lem7127644 A s)). Qed.
Lemma lem7127646 {A : Type'} (s : A -> Prop) : (term475 A s) = (term495 A s).
Proof. exact (EQ_MP (@lem7127645 A s) (@lem7127623 A s)). Qed.
Lemma lem7127751 {A : Type'} (s : A -> Prop) : (term451 A s) = (term495 A s).
Proof. exact (TRANS (@lem7127619 A s) (@lem7127646 A s)). Qed.
Lemma lem7127752 {A : Type'} : (term452 A) = (term496 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127751 A s)). Qed.
Lemma lem7127753 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127754 {A : Type'} : (term453 A) = (term497 A).
Proof. exact (MK_COMB (@lem7127753 A) (@lem7127752 A)). Qed.
Lemma lem7127756 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7127757 {A : Type'} (P : type686 A) (Q : type686 A) : (term231 A P Q) = (term232 A P Q).
Proof. exact (@lem7127756 (A -> Prop) P Q). Qed.
Lemma lem7127758 {A : Type'} : (term498 A) = (term499 A).
Proof. exact (@lem7127757 A (term500 A) (term501 A)). Qed.
Lemma lem7127759 {A : Type'} (s : A -> Prop) : (term502 A s) = (term489 A s).
Proof. exact (eq_refl (term502 A s)). Qed.
Lemma lem7127760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127761 {A : Type'} (s : A -> Prop) : (term503 A s) = (term491 A s).
Proof. exact (MK_COMB (@lem7127760) (@lem7127759 A s)). Qed.
Lemma lem7127762 {A : Type'} (s : A -> Prop) : (term504 A s) = (term494 A s).
Proof. exact (eq_refl (term504 A s)). Qed.
Lemma lem7127763 {A : Type'} (s : A -> Prop) : (term505 A s) = (term495 A s).
Proof. exact (MK_COMB (@lem7127761 A s) (@lem7127762 A s)). Qed.
Lemma lem7127764 {A : Type'} : (term506 A) = (term496 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127763 A s)). Qed.
Lemma lem7127765 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127766 {A : Type'} : (term498 A) = (term497 A).
Proof. exact (MK_COMB (@lem7127765 A) (@lem7127764 A)). Qed.
Lemma lem7127767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7127768 {A : Type'} : (term507 A) = (term508 A).
Proof. exact (MK_COMB (@lem7127767) (@lem7127766 A)). Qed.
Lemma lem7127769 {A : Type'} (s : A -> Prop) : (term502 A s) = (term489 A s).
Proof. exact (eq_refl (term502 A s)). Qed.
Lemma lem7127770 {A : Type'} : (term509 A) = (term500 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127769 A s)). Qed.
Lemma lem7127771 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127772 {A : Type'} : (term510 A) = (term511 A).
Proof. exact (MK_COMB (@lem7127771 A) (@lem7127770 A)). Qed.
Lemma lem7127773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7127774 {A : Type'} : (term512 A) = (term513 A).
Proof. exact (MK_COMB (@lem7127773) (@lem7127772 A)). Qed.
Lemma lem7127775 {A : Type'} (s : A -> Prop) : (term504 A s) = (term494 A s).
Proof. exact (eq_refl (term504 A s)). Qed.
Lemma lem7127776 {A : Type'} : (term514 A) = (term501 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127775 A s)). Qed.
Lemma lem7127777 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127778 {A : Type'} : (term515 A) = (term516 A).
Proof. exact (MK_COMB (@lem7127777 A) (@lem7127776 A)). Qed.
Lemma lem7127779 {A : Type'} : (term499 A) = (term517 A).
Proof. exact (MK_COMB (@lem7127774 A) (@lem7127778 A)). Qed.
Lemma lem7127780 {A : Type'} : ((term498 A) = (term499 A)) = ((term497 A) = (term517 A)).
Proof. exact (MK_COMB (@lem7127768 A) (@lem7127779 A)). Qed.
Lemma lem7127781 {A : Type'} : (term497 A) = (term517 A).
Proof. exact (EQ_MP (@lem7127780 A) (@lem7127758 A)). Qed.
Lemma lem7127896 {A : Type'} : (term453 A) = (term517 A).
Proof. exact (TRANS (@lem7127754 A) (@lem7127781 A)). Qed.
Lemma lem7127897 {A : Type'} : (term104 A) = (term517 A).
Proof. exact (TRANS (@lem7127485 A) (@lem7127896 A)). Qed.
Lemma lem7127898 {A : Type'} (h1 : term104 A) : term517 A.
Proof. exact (EQ_MP (@lem7127897 A) (@lem7126206 A h1)). Qed.
Lemma lem7127899 {A : Type'} (x : type638 A) (h1 : term356 A x) : term356 A x.
Proof. exact (h1). Qed.
Lemma lem7127933 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term171 A v u f x) = (term171 A v u f x).
Proof. exact (eq_refl (term171 A v u f x)). Qed.
Lemma lem7127934 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term172 A v u f) = (term172 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7127933 A v u f x)). Qed.
Lemma lem7127935 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127936 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term173 A v u f) = (term173 A v u f).
Proof. exact (MK_COMB (@lem7127935 A) (@lem7127934 A v u f)). Qed.
Lemma lem7127937 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term173 A v u f.
Proof. exact (EQ_MP (@lem7127936 A v u f) (@lem7126283 A v u f h1)). Qed.
Lemma lem7127966 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term360 A s x t) = (term360 A s x t).
Proof. exact (eq_refl (term360 A s x t)). Qed.
Lemma lem7127967 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term377 A s t) = (term377 A s t).
Proof. exact (fun_ext (fun x : A => @lem7127966 A s x t)). Qed.
Lemma lem7127968 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7127969 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term392 A s t) = (term392 A s t).
Proof. exact (MK_COMB (@lem7127968 A) (@lem7127967 A s t)). Qed.
Lemma lem7127970 {A : Type'} (s : A -> Prop) : (term399 A s) = (term399 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7127969 A s t)). Qed.
Lemma lem7127971 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127972 {A : Type'} (s : A -> Prop) : (term414 A s) = (term414 A s).
Proof. exact (MK_COMB (@lem7127971 A) (@lem7127970 A s)). Qed.
Lemma lem7127973 {A : Type'} : (term421 A) = (term421 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7127972 A s)). Qed.
Lemma lem7127974 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7127975 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (MK_COMB (@lem7127974 A) (@lem7127973 A)). Qed.
Lemma lem7128002 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term363 A s x t) = (term363 A s x t).
Proof. exact (eq_refl (term363 A s x t)). Qed.
Lemma lem7128003 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term376 A s t) = (term376 A s t).
Proof. exact (fun_ext (fun x : A => @lem7128002 A s x t)). Qed.
Lemma lem7128004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128005 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term387 A s t) = (term387 A s t).
Proof. exact (MK_COMB (@lem7128004 A) (@lem7128003 A s t)). Qed.
Lemma lem7128006 {A : Type'} (s : A -> Prop) : (term398 A s) = (term398 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128005 A s t)). Qed.
Lemma lem7128007 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128008 {A : Type'} (s : A -> Prop) : (term409 A s) = (term409 A s).
Proof. exact (MK_COMB (@lem7128007 A) (@lem7128006 A s)). Qed.
Lemma lem7128009 {A : Type'} : (term420 A) = (term420 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128008 A s)). Qed.
Lemma lem7128010 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128011 {A : Type'} : (term431 A) = (term431 A).
Proof. exact (MK_COMB (@lem7128010 A) (@lem7128009 A)). Qed.
Lemma lem7128012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7128013 {A : Type'} : (term433 A) = (term433 A).
Proof. exact (MK_COMB (@lem7128012) (@lem7128011 A)). Qed.
Lemma lem7128014 {A : Type'} : (term437 A) = (term437 A).
Proof. exact (MK_COMB (@lem7128013 A) (@lem7127975 A)). Qed.
Lemma lem7128015 {A : Type'} (h1 : term105 A) : term437 A.
Proof. exact (EQ_MP (@lem7128014 A) (@lem7127451 A h1)). Qed.
Lemma lem7128042 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term440 A s x t) = (term440 A s x t).
Proof. exact (eq_refl (term440 A s x t)). Qed.
Lemma lem7128043 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term457 A s t) = (term457 A s t).
Proof. exact (fun_ext (fun x : A => @lem7128042 A s x t)). Qed.
Lemma lem7128044 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128045 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term472 A s t) = (term472 A s t).
Proof. exact (MK_COMB (@lem7128044 A) (@lem7128043 A s t)). Qed.
Lemma lem7128046 {A : Type'} (s : A -> Prop) : (term479 A s) = (term479 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128045 A s t)). Qed.
Lemma lem7128047 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128048 {A : Type'} (s : A -> Prop) : (term494 A s) = (term494 A s).
Proof. exact (MK_COMB (@lem7128047 A) (@lem7128046 A s)). Qed.
Lemma lem7128049 {A : Type'} : (term501 A) = (term501 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128048 A s)). Qed.
Lemma lem7128050 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128051 {A : Type'} : (term516 A) = (term516 A).
Proof. exact (MK_COMB (@lem7128050 A) (@lem7128049 A)). Qed.
Lemma lem7128080 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term443 A s x t) = (term443 A s x t).
Proof. exact (eq_refl (term443 A s x t)). Qed.
Lemma lem7128081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term456 A s t) = (term456 A s t).
Proof. exact (fun_ext (fun x : A => @lem7128080 A s x t)). Qed.
Lemma lem7128082 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term467 A s t) = (term467 A s t).
Proof. exact (MK_COMB (@lem7128082 A) (@lem7128081 A s t)). Qed.
Lemma lem7128084 {A : Type'} (s : A -> Prop) : (term478 A s) = (term478 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128083 A s t)). Qed.
Lemma lem7128085 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128086 {A : Type'} (s : A -> Prop) : (term489 A s) = (term489 A s).
Proof. exact (MK_COMB (@lem7128085 A) (@lem7128084 A s)). Qed.
Lemma lem7128087 {A : Type'} : (term500 A) = (term500 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128086 A s)). Qed.
Lemma lem7128088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128089 {A : Type'} : (term511 A) = (term511 A).
Proof. exact (MK_COMB (@lem7128088 A) (@lem7128087 A)). Qed.
Lemma lem7128090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7128091 {A : Type'} : (term513 A) = (term513 A).
Proof. exact (MK_COMB (@lem7128090) (@lem7128089 A)). Qed.
Lemma lem7128092 {A : Type'} : (term517 A) = (term517 A).
Proof. exact (MK_COMB (@lem7128091 A) (@lem7128051 A)). Qed.
Lemma lem7128093 {A : Type'} (h1 : term104 A) : term517 A.
Proof. exact (EQ_MP (@lem7128092 A) (@lem7127898 A h1)). Qed.
Lemma lem7128108 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term165 A s x t) = (term165 A s x t).
Proof. exact (eq_refl (term165 A s x t)). Qed.
Lemma lem7128109 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term213 A s t) = (term213 A s t).
Proof. exact (fun_ext (fun x : A => @lem7128108 A s x t)). Qed.
Lemma lem7128110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128111 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term214 A s t) = (term214 A s t).
Proof. exact (MK_COMB (@lem7128110 A) (@lem7128109 A s t)). Qed.
Lemma lem7128120 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term215 A s t) = (term215 A s t).
Proof. exact (eq_refl (term215 A s t)). Qed.
Lemma lem7128121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term217 A s t).
Proof. exact (MK_COMB (@lem7128120 A s t) (@lem7128111 A s t)). Qed.
Lemma lem7128122 {A : Type'} (s : A -> Prop) : (term236 A s) = (term236 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128121 A s t)). Qed.
Lemma lem7128123 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128124 {A : Type'} (s : A -> Prop) : (term251 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem7128123 A) (@lem7128122 A s)). Qed.
Lemma lem7128125 {A : Type'} : (term258 A) = (term258 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128124 A s)). Qed.
Lemma lem7128126 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128127 {A : Type'} : (term273 A) = (term273 A).
Proof. exact (MK_COMB (@lem7128126 A) (@lem7128125 A)). Qed.
Lemma lem7128158 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term518 A x s t) = (term518 A x s t).
Proof. exact (eq_refl (term518 A x s t)). Qed.
Lemma lem7128159 {A : Type'} (x : type638 A) (s : A -> Prop) : (term519 A x s) = (term519 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128158 A x s t)). Qed.
Lemma lem7128160 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128161 {A : Type'} (x : type638 A) (s : A -> Prop) : (term331 A x s) = (term331 A x s).
Proof. exact (MK_COMB (@lem7128160 A) (@lem7128159 A x s)). Qed.
Lemma lem7128162 {A : Type'} (x : type638 A) : (term333 A x) = (term333 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128161 A x s)). Qed.
Lemma lem7128163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128164 {A : Type'} (x : type638 A) : (term335 A x) = (term335 A x).
Proof. exact (MK_COMB (@lem7128163 A) (@lem7128162 A x)). Qed.
Lemma lem7128165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7128166 {A : Type'} (x : type638 A) : (term354 A x) = (term354 A x).
Proof. exact (MK_COMB (@lem7128165) (@lem7128164 A x)). Qed.
Lemma lem7128167 {A : Type'} (x : type638 A) : (term356 A x) = (term356 A x).
Proof. exact (MK_COMB (@lem7128166 A x) (@lem7128127 A)). Qed.
Lemma lem7128168 {A : Type'} (x : type638 A) (h1 : term356 A x) : term356 A x.
Proof. exact (EQ_MP (@lem7128167 A x) (@lem7127899 A x h1)). Qed.
Lemma lem7128226 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term201 A v u f x') : term201 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem7128228 {A : Type'} (x : type638 A) (h1 : term356 A x) : term335 A x.
Proof. exact (proj1 (@lem7128168 A x h1)). Qed.
Lemma lem7128229 {A : Type'} (h1 : term104 A) : term516 A.
Proof. exact (proj2 (@lem7128093 A h1)). Qed.
Lemma lem7128230 {A : Type'} (h1 : term104 A) : term511 A.
Proof. exact (proj1 (@lem7128093 A h1)). Qed.
Lemma lem7128231 {A : Type'} (h1 : term105 A) : term436 A.
Proof. exact (proj2 (@lem7128015 A h1)). Qed.
Lemma lem7128234 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term175 A v u f x'.
Proof. exact (h1). Qed.
Lemma lem7128236 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term176 A v x' u.
Proof. exact (proj1 (@lem7128234 A v u f x' h1)). Qed.
Lemma lem7128279 {A : Type'} (x : type638 A) (s : A -> Prop) (t : A -> Prop) : (term518 A x s t) = (term520 A x s t).
Proof. exact (@lem19490 (term521 A x t s) (@SUBSET A s t) (term522 A x s t)). Qed.
Lemma lem7128280 {A : Type'} (x : type638 A) (s : A -> Prop) : (term519 A x s) = (term523 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128279 A x s t)). Qed.
Lemma lem7128281 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128282 {A : Type'} (x : type638 A) (s : A -> Prop) : (term331 A x s) = (term524 A x s).
Proof. exact (MK_COMB (@lem7128281 A) (@lem7128280 A x s)). Qed.
Lemma lem7128283 {A : Type'} (x : type638 A) : (term333 A x) = (term525 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128282 A x s)). Qed.
Lemma lem7128284 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128286 {A : Type'} (x : type638 A) : (term335 A x) = (term526 A x).
Proof. exact (MK_COMB (@lem7128284 A) (@lem7128283 A x)). Qed.
Lemma lem7128287 {A : Type'} (x : type638 A) (h1 : term356 A x) : term526 A x.
Proof. exact (EQ_MP (@lem7128286 A x) (@lem7128228 A x h1)). Qed.
Lemma lem7128355 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term443 A s x t) = (term527 A s x t).
Proof. exact (@lem19490 (term16 A x s) (term3 A x s t) (term16 A x t)). Qed.
Lemma lem7128356 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term456 A s t) = (term528 A s t).
Proof. exact (fun_ext (fun x : A => @lem7128355 A s x t)). Qed.
Lemma lem7128357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128358 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term467 A s t) = (term529 A s t).
Proof. exact (MK_COMB (@lem7128357 A) (@lem7128356 A s t)). Qed.
Lemma lem7128359 {A : Type'} (s : A -> Prop) : (term478 A s) = (term530 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128358 A s t)). Qed.
Lemma lem7128360 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128361 {A : Type'} (s : A -> Prop) : (term489 A s) = (term531 A s).
Proof. exact (MK_COMB (@lem7128360 A) (@lem7128359 A s)). Qed.
Lemma lem7128362 {A : Type'} : (term500 A) = (term532 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128361 A s)). Qed.
Lemma lem7128363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128365 {A : Type'} : (term511 A) = (term533 A).
Proof. exact (MK_COMB (@lem7128363 A) (@lem7128362 A)). Qed.
Lemma lem7128366 {A : Type'} (h1 : term104 A) : term533 A.
Proof. exact (EQ_MP (@lem7128365 A) (@lem7128230 A h1)). Qed.
Lemma lem7128449 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term194 A v u) : term194 A v u.
Proof. exact (h1). Qed.
Lemma lem7128467 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term171 A v u f x) = (term171 A v u f x).
Proof. exact (eq_refl (term171 A v u f x)). Qed.
Lemma lem7128468 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term172 A v u f) = (term172 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7128467 A v u f x)). Qed.
Lemma lem7128469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128471 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term173 A v u f) = (term173 A v u f).
Proof. exact (MK_COMB (@lem7128469 A) (@lem7128468 A v u f)). Qed.
Lemma lem7128472 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term173 A v u f.
Proof. exact (EQ_MP (@lem7128471 A v u f) (@lem7127937 A v u f h1)). Qed.
Lemma lem7128591 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term440 A s x t) = (term440 A s x t).
Proof. exact (eq_refl (term440 A s x t)). Qed.
Lemma lem7128592 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term457 A s t) = (term457 A s t).
Proof. exact (fun_ext (fun x : A => @lem7128591 A s x t)). Qed.
Lemma lem7128593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128594 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term472 A s t) = (term472 A s t).
Proof. exact (MK_COMB (@lem7128593 A) (@lem7128592 A s t)). Qed.
Lemma lem7128595 {A : Type'} (s : A -> Prop) : (term479 A s) = (term479 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128594 A s t)). Qed.
Lemma lem7128596 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128597 {A : Type'} (s : A -> Prop) : (term494 A s) = (term494 A s).
Proof. exact (MK_COMB (@lem7128596 A) (@lem7128595 A s)). Qed.
Lemma lem7128598 {A : Type'} : (term501 A) = (term501 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128597 A s)). Qed.
Lemma lem7128599 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128601 {A : Type'} : (term516 A) = (term516 A).
Proof. exact (MK_COMB (@lem7128599 A) (@lem7128598 A)). Qed.
Lemma lem7128602 {A : Type'} (h1 : term104 A) : term516 A.
Proof. exact (EQ_MP (@lem7128601 A) (@lem7128229 A h1)). Qed.
Lemma lem7128645 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term360 A s x t) = (term534 A s x t).
Proof. exact (@lem19490 (@IN A x s) (term535 A x s t) (term16 A x t)). Qed.
Lemma lem7128646 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term377 A s t) = (term536 A s t).
Proof. exact (fun_ext (fun x : A => @lem7128645 A s x t)). Qed.
Lemma lem7128647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7128648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term392 A s t) = (term537 A s t).
Proof. exact (MK_COMB (@lem7128647 A) (@lem7128646 A s t)). Qed.
Lemma lem7128649 {A : Type'} (s : A -> Prop) : (term399 A s) = (term538 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7128648 A s t)). Qed.
Lemma lem7128650 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128651 {A : Type'} (s : A -> Prop) : (term414 A s) = (term539 A s).
Proof. exact (MK_COMB (@lem7128650 A) (@lem7128649 A s)). Qed.
Lemma lem7128652 {A : Type'} : (term421 A) = (term540 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7128651 A s)). Qed.
Lemma lem7128653 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7128655 {A : Type'} : (term436 A) = (term541 A).
Proof. exact (MK_COMB (@lem7128653 A) (@lem7128652 A)). Qed.
Lemma lem7128656 {A : Type'} (h1 : term105 A) : term541 A.
Proof. exact (EQ_MP (@lem7128655 A) (@lem7128231 A h1)). Qed.
Lemma lem7128672 {A : Type'} (_95085 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term542 A x _95085.
Proof. exact (@lem7128287 A x h1 _95085). Qed.
Lemma lem7128673 {A : Type'} (x : type638 A) (_95085 : A -> Prop) : (term542 A x _95085) = (term524 A x _95085).
Proof. exact (eq_refl (term542 A x _95085)). Qed.
Lemma lem7128674 {A : Type'} (_95085 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term524 A x _95085.
Proof. exact (EQ_MP (@lem7128673 A x _95085) (@lem7128672 A _95085 x h1)). Qed.
Lemma lem7128675 {A : Type'} (_95085 : A -> Prop) (_95086 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term543 A x _95085 _95086.
Proof. exact (@lem7128674 A _95085 x h1 _95086). Qed.
Lemma lem7128676 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term543 A x _95085 _95086) = (term520 A x _95085 _95086).
Proof. exact (eq_refl (term543 A x _95085 _95086)). Qed.
Lemma lem7128677 {A : Type'} (_95085 : A -> Prop) (_95086 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term520 A x _95085 _95086.
Proof. exact (EQ_MP (@lem7128676 A x _95085 _95086) (@lem7128675 A _95085 _95086 x h1)). Qed.
Lemma lem7128687 {A : Type'} (_95090 : A -> Prop) (h1 : term104 A) : term544 A _95090.
Proof. exact (@lem7128366 A h1 _95090). Qed.
Lemma lem7128688 {A : Type'} (_95090 : A -> Prop) : (term544 A _95090) = (term531 A _95090).
Proof. exact (eq_refl (term544 A _95090)). Qed.
Lemma lem7128689 {A : Type'} (_95090 : A -> Prop) (h1 : term104 A) : term531 A _95090.
Proof. exact (EQ_MP (@lem7128688 A _95090) (@lem7128687 A _95090 h1)). Qed.
Lemma lem7128690 {A : Type'} (_95090 : A -> Prop) (_95091 : A -> Prop) (h1 : term104 A) : term545 A _95090 _95091.
Proof. exact (@lem7128689 A _95090 h1 _95091). Qed.
Lemma lem7128691 {A : Type'} (_95090 : A -> Prop) (_95091 : A -> Prop) : (term545 A _95090 _95091) = (term529 A _95090 _95091).
Proof. exact (eq_refl (term545 A _95090 _95091)). Qed.
Lemma lem7128692 {A : Type'} (_95090 : A -> Prop) (_95091 : A -> Prop) (h1 : term104 A) : term529 A _95090 _95091.
Proof. exact (EQ_MP (@lem7128691 A _95090 _95091) (@lem7128690 A _95090 _95091 h1)). Qed.
Lemma lem7128693 {A : Type'} (_95090 : A -> Prop) (_95091 : A -> Prop) (_95092 : A) (h1 : term104 A) : term546 A _95090 _95091 _95092.
Proof. exact (@lem7128692 A _95090 _95091 h1 _95092). Qed.
Lemma lem7128694 {A : Type'} (_95090 : A -> Prop) (_95092 : A) (_95091 : A -> Prop) : (term546 A _95090 _95091 _95092) = (term527 A _95090 _95092 _95091).
Proof. exact (eq_refl (term546 A _95090 _95091 _95092)). Qed.
Lemma lem7128695 {A : Type'} (_95090 : A -> Prop) (_95092 : A) (_95091 : A -> Prop) (h1 : term104 A) : term527 A _95090 _95092 _95091.
Proof. exact (EQ_MP (@lem7128694 A _95090 _95092 _95091) (@lem7128693 A _95090 _95091 _95092 h1)). Qed.
Lemma lem7128723 {A : Type'} (_95102 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term547 A v u f _95102.
Proof. exact (@lem7128472 A v u f h1 _95102). Qed.
Lemma lem7128724 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_95102 : A) : (term547 A v u f _95102) = (term171 A v u f _95102).
Proof. exact (eq_refl (term547 A v u f _95102)). Qed.
Lemma lem7128725 {A : Type'} (_95102 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term171 A v u f _95102.
Proof. exact (EQ_MP (@lem7128724 A v u f _95102) (@lem7128723 A _95102 v u f h1)). Qed.
Lemma lem7128750 {A : Type'} (_95111 : A -> Prop) (h1 : term104 A) : term504 A _95111.
Proof. exact (@lem7128602 A h1 _95111). Qed.
Lemma lem7128751 {A : Type'} (_95111 : A -> Prop) : (term504 A _95111) = (term494 A _95111).
Proof. exact (eq_refl (term504 A _95111)). Qed.
Lemma lem7128752 {A : Type'} (_95111 : A -> Prop) (h1 : term104 A) : term494 A _95111.
Proof. exact (EQ_MP (@lem7128751 A _95111) (@lem7128750 A _95111 h1)). Qed.
Lemma lem7128753 {A : Type'} (_95111 : A -> Prop) (_95112 : A -> Prop) (h1 : term104 A) : term482 A _95111 _95112.
Proof. exact (@lem7128752 A _95111 h1 _95112). Qed.
Lemma lem7128754 {A : Type'} (_95111 : A -> Prop) (_95112 : A -> Prop) : (term482 A _95111 _95112) = (term472 A _95111 _95112).
Proof. exact (eq_refl (term482 A _95111 _95112)). Qed.
Lemma lem7128755 {A : Type'} (_95111 : A -> Prop) (_95112 : A -> Prop) (h1 : term104 A) : term472 A _95111 _95112.
Proof. exact (EQ_MP (@lem7128754 A _95111 _95112) (@lem7128753 A _95111 _95112 h1)). Qed.
Lemma lem7128756 {A : Type'} (_95111 : A -> Prop) (_95112 : A -> Prop) (_95113 : A) (h1 : term104 A) : term460 A _95111 _95112 _95113.
Proof. exact (@lem7128755 A _95111 _95112 h1 _95113). Qed.
Lemma lem7128757 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : (term460 A _95111 _95112 _95113) = (term440 A _95111 _95113 _95112).
Proof. exact (eq_refl (term460 A _95111 _95112 _95113)). Qed.
Lemma lem7128768 {A : Type'} (_95117 : A -> Prop) (h1 : term105 A) : term548 A _95117.
Proof. exact (@lem7128656 A h1 _95117). Qed.
Lemma lem7128769 {A : Type'} (_95117 : A -> Prop) : (term548 A _95117) = (term539 A _95117).
Proof. exact (eq_refl (term548 A _95117)). Qed.
Lemma lem7128770 {A : Type'} (_95117 : A -> Prop) (h1 : term105 A) : term539 A _95117.
Proof. exact (EQ_MP (@lem7128769 A _95117) (@lem7128768 A _95117 h1)). Qed.
Lemma lem7128771 {A : Type'} (_95117 : A -> Prop) (_95118 : A -> Prop) (h1 : term105 A) : term549 A _95117 _95118.
Proof. exact (@lem7128770 A _95117 h1 _95118). Qed.
Lemma lem7128772 {A : Type'} (_95117 : A -> Prop) (_95118 : A -> Prop) : (term549 A _95117 _95118) = (term537 A _95117 _95118).
Proof. exact (eq_refl (term549 A _95117 _95118)). Qed.
Lemma lem7128773 {A : Type'} (_95117 : A -> Prop) (_95118 : A -> Prop) (h1 : term105 A) : term537 A _95117 _95118.
Proof. exact (EQ_MP (@lem7128772 A _95117 _95118) (@lem7128771 A _95117 _95118 h1)). Qed.
Lemma lem7128774 {A : Type'} (_95117 : A -> Prop) (_95118 : A -> Prop) (_95119 : A) (h1 : term105 A) : term550 A _95117 _95118 _95119.
Proof. exact (@lem7128773 A _95117 _95118 h1 _95119). Qed.
Lemma lem7128775 {A : Type'} (_95117 : A -> Prop) (_95119 : A) (_95118 : A -> Prop) : (term550 A _95117 _95118 _95119) = (term534 A _95117 _95119 _95118).
Proof. exact (eq_refl (term550 A _95117 _95118 _95119)). Qed.
Lemma lem7128776 {A : Type'} (_95117 : A -> Prop) (_95119 : A) (_95118 : A -> Prop) (h1 : term105 A) : term534 A _95117 _95119 _95118.
Proof. exact (EQ_MP (@lem7128775 A _95117 _95119 _95118) (@lem7128774 A _95117 _95118 _95119 h1)). Qed.
Lemma lem7128834 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term194 A v u) : term194 A v u.
Proof. exact (h1). Qed.
Lemma lem7128852 {A : Type'} (_95091 : A -> Prop) (_95092 : A) (_95090 : A -> Prop) (h1 : term104 A) : term551 A _95091 _95092 _95090.
Proof. exact (proj1 (@lem7128695 A _95090 _95092 _95091 h1)). Qed.
Lemma lem7128864 {A : Type'} (_95086 : A -> Prop) (_95085 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term552 A x _95086 _95085.
Proof. exact (proj1 (@lem7128677 A _95085 _95086 x h1)). Qed.
Lemma lem7128870 {A : Type'} (_95085 : A -> Prop) (_95086 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term553 A x _95085 _95086.
Proof. exact (proj2 (@lem7128677 A _95085 _95086 x h1)). Qed.
Lemma lem7128883 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_95102 : A) : (term171 A v u f _95102) = (term554 A v u f _95102).
Proof. exact (@lem7125761 (term16 A _95102 v) (@IN A _95102 u) ((f _95102) = term167)). Qed.
Lemma lem7128884 {A : Type'} (_95102 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term554 A v u f _95102.
Proof. exact (EQ_MP (@lem7128883 A v u f _95102) (@lem7128725 A _95102 v u f h1)). Qed.
Lemma lem7128904 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) (h1 : term104 A) : term440 A _95111 _95113 _95112.
Proof. exact (EQ_MP (@lem7128757 A _95111 _95113 _95112) (@lem7128756 A _95111 _95112 _95113 h1)). Qed.
Lemma lem7128920 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term16 A x' u.
Proof. exact (proj2 (@lem7128236 A v u f x' h1)). Qed.
Lemma lem7128926 {A : Type'} (_95118 : A -> Prop) (_95119 : A) (_95117 : A -> Prop) (h1 : term105 A) : term555 A _95118 _95119 _95117.
Proof. exact (proj1 (@lem7128776 A _95117 _95119 _95118 h1)). Qed.
Lemma lem7129086 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term194 A v u) : term194 A v u.
Proof. exact (h1). Qed.
Lemma lem7129087 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term194 A v u) : term556 A v u.
Proof. exact (fun h0 : term189 A v u => @lem7129086 A v u h1). Qed.
Lemma lem7129089 (p : Prop) : (term557 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7129090 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term556 A v u) = (term194 A v u).
Proof. exact (@lem7129089 (term189 A v u)). Qed.
Lemma lem7129091 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term194 A v u) : term194 A v u.
Proof. exact (EQ_MP (@lem7129090 A v u) (@lem7129087 A v u h1)). Qed.
Lemma lem7129097 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7129098 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term552 A x _95086 _95085) = (term558 A x _95085 _95086).
Proof. exact (@lem7129097 (term521 A x _95086 _95085) (@SUBSET A _95085 _95086)). Qed.
Lemma lem7129104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7129105 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term559 A x _95086 _95085) = (term560 A x _95085 _95086).
Proof. exact (MK_COMB (@lem7129104) (@lem7129098 A x _95085 _95086)). Qed.
Lemma lem7129111 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term558 A x _95085 _95086) = (term558 A x _95085 _95086).
Proof. exact (eq_refl (term558 A x _95085 _95086)). Qed.
Lemma lem7129112 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : ((term552 A x _95086 _95085) = (term558 A x _95085 _95086)) = ((term558 A x _95085 _95086) = (term558 A x _95085 _95086)).
Proof. exact (MK_COMB (@lem7129105 A x _95085 _95086) (@lem7129111 A x _95085 _95086)). Qed.
Lemma lem7129114 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7129115 (x : Prop) : (x = x) = True.
Proof. exact (@lem7129114 Prop x). Qed.
Lemma lem7129116 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : ((term558 A x _95085 _95086) = (term558 A x _95085 _95086)) = True.
Proof. exact (@lem7129115 (term558 A x _95085 _95086)). Qed.
Lemma lem7129117 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : ((term552 A x _95086 _95085) = (term558 A x _95085 _95086)) = True.
Proof. exact (TRANS (@lem7129112 A x _95085 _95086) (@lem7129116 A x _95085 _95086)). Qed.
Lemma lem7129118 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : True = ((term552 A x _95086 _95085) = (term558 A x _95085 _95086)).
Proof. exact (SYM (@lem7129117 A x _95085 _95086)). Qed.
Lemma lem7129119 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term552 A x _95086 _95085) = (term558 A x _95085 _95086).
Proof. exact (EQ_MP (@lem7129118 A x _95085 _95086) (@lem0)). Qed.
Lemma lem7129120 {A : Type'} (_95085 : A -> Prop) (_95086 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term558 A x _95085 _95086.
Proof. exact (EQ_MP (@lem7129119 A x _95085 _95086) (@lem7128864 A _95086 _95085 x h1)). Qed.
Lemma lem7129122 (b : Prop) (a : Prop) : (a \/ b) = (term561 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7129125 {A : Type'} (x : type638 A) (_95086 : A -> Prop) (_95085 : A -> Prop) : (term558 A x _95085 _95086) = (term562 A x _95086 _95085).
Proof. exact (@lem7129122 (@SUBSET A _95085 _95086) (term521 A x _95086 _95085)). Qed.
Lemma lem7129128 {A : Type'} (_95086 : A -> Prop) (_95085 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term562 A x _95086 _95085.
Proof. exact (EQ_MP (@lem7129125 A x _95086 _95085) (@lem7129120 A _95085 _95086 x h1)). Qed.
Lemma lem7129129 {A : Type'} (_95086 : A -> Prop) (_95085 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term562 A x _95086 _95085.
Proof. exact (@lem7129128 A _95086 _95085 x h1). Qed.
Lemma lem7129130 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term356 A x) : term563 A x v u.
Proof. exact (@lem7129129 A (term1 A v u) u x h1). Qed.
Lemma lem7129133 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term194 A v u) (h2 : term356 A x) : term564 A x v u.
Proof. exact (@lem7129130 A v u x h2 (@lem7129091 A v u h1)). Qed.
Lemma lem7129134 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term194 A v u) (h2 : term356 A x) : term565 A x v u.
Proof. exact (fun h0 : term566 A x v u => @lem7129133 A v u x h1 h2). Qed.
Lemma lem7129136 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7129137 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) : (term565 A x v u) = (term564 A x v u).
Proof. exact (@lem7129136 (term564 A x v u)). Qed.
Lemma lem7129138 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term194 A v u) (h2 : term356 A x) : term564 A x v u.
Proof. exact (EQ_MP (@lem7129137 A x v u) (@lem7129134 A v u x h1 h2)). Qed.
Lemma lem7129140 (b : Prop) (a : Prop) : (a \/ b) = (term561 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7129141 {A : Type'} (_95092 : A) (_95090 : A -> Prop) (_95091 : A -> Prop) : (term551 A _95091 _95092 _95090) = (term567 A _95092 _95090 _95091).
Proof. exact (@lem7129140 (term16 A _95092 _95090) (term3 A _95092 _95090 _95091)). Qed.
Lemma lem7129143 (a : Prop) : (term30 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7129144 {A : Type'} (_95092 : A) (_95090 : A -> Prop) : (term162 A _95092 _95090) = (@IN A _95092 _95090).
Proof. exact (@lem7129143 (@IN A _95092 _95090)). Qed.
Lemma lem7129145 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129146 {A : Type'} (_95092 : A) (_95090 : A -> Prop) : (term568 A _95092 _95090) = (term569 A _95092 _95090).
Proof. exact (MK_COMB (@lem7129145) (@lem7129144 A _95092 _95090)). Qed.
Lemma lem7129147 {A : Type'} (_95092 : A) (_95090 : A -> Prop) (_95091 : A -> Prop) : (term3 A _95092 _95090 _95091) = (term3 A _95092 _95090 _95091).
Proof. exact (eq_refl (term3 A _95092 _95090 _95091)). Qed.
Lemma lem7129148 {A : Type'} (_95092 : A) (_95090 : A -> Prop) (_95091 : A -> Prop) : (term567 A _95092 _95090 _95091) = (term570 A _95092 _95090 _95091).
Proof. exact (MK_COMB (@lem7129146 A _95092 _95090) (@lem7129147 A _95092 _95090 _95091)). Qed.
Lemma lem7129149 {A : Type'} (_95092 : A) (_95090 : A -> Prop) (_95091 : A -> Prop) : (term551 A _95091 _95092 _95090) = (term570 A _95092 _95090 _95091).
Proof. exact (TRANS (@lem7129141 A _95092 _95090 _95091) (@lem7129148 A _95092 _95090 _95091)). Qed.
Lemma lem7129152 {A : Type'} (_95092 : A) (_95090 : A -> Prop) (_95091 : A -> Prop) (h1 : term104 A) : term570 A _95092 _95090 _95091.
Proof. exact (EQ_MP (@lem7129149 A _95092 _95090 _95091) (@lem7128852 A _95091 _95092 _95090 h1)). Qed.
Lemma lem7129153 {A : Type'} (_95092 : A) (_95090 : A -> Prop) (_95091 : A -> Prop) (h1 : term104 A) : term570 A _95092 _95090 _95091.
Proof. exact (@lem7129152 A _95092 _95090 _95091 h1). Qed.
Lemma lem7129154 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (_95091 : A -> Prop) (h1 : term104 A) : term571 A x v u _95091.
Proof. exact (@lem7129153 A (term572 A x v u) u _95091 h1). Qed.
Lemma lem7129157 {A : Type'} (_95091 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : term573 A x v u _95091.
Proof. exact (@lem7129154 A x v u _95091 h1 (@lem7129138 A v u x h2 h3)). Qed.
Lemma lem7129158 {A : Type'} (_95091 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : term573 A x v u _95091.
Proof. exact (@lem7129157 A _95091 v u x h1 h2 h3). Qed.
Lemma lem7129159 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : term574 A x v u.
Proof. exact (@lem7129158 A (@DIFF A v u) v u x h1 h2 h3). Qed.
Lemma lem7129160 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : term575 A x v u.
Proof. exact (fun h0 : term576 A x v u => @lem7129159 A v u x h1 h2 h3). Qed.
Lemma lem7129162 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7129163 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) : (term575 A x v u) = (term574 A x v u).
Proof. exact (@lem7129162 (term574 A x v u)). Qed.
Lemma lem7129164 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : term574 A x v u.
Proof. exact (EQ_MP (@lem7129163 A x v u) (@lem7129160 A v u x h1 h2 h3)). Qed.
Lemma lem7129166 (b : Prop) (a : Prop) : (a \/ b) = (term561 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7129167 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term553 A x _95085 _95086) = (term577 A x _95085 _95086).
Proof. exact (@lem7129166 (term522 A x _95085 _95086) (@SUBSET A _95085 _95086)). Qed.
Lemma lem7129169 (a : Prop) : (term30 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7129170 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term578 A x _95085 _95086) = (term579 A x _95085 _95086).
Proof. exact (@lem7129169 (term579 A x _95085 _95086)). Qed.
Lemma lem7129171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129172 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term580 A x _95085 _95086) = (term581 A x _95085 _95086).
Proof. exact (MK_COMB (@lem7129171) (@lem7129170 A x _95085 _95086)). Qed.
Lemma lem7129173 {A : Type'} (_95085 : A -> Prop) (_95086 : A -> Prop) : (@SUBSET A _95085 _95086) = (@SUBSET A _95085 _95086).
Proof. exact (eq_refl (@SUBSET A _95085 _95086)). Qed.
Lemma lem7129174 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term577 A x _95085 _95086) = (term582 A x _95085 _95086).
Proof. exact (MK_COMB (@lem7129172 A x _95085 _95086) (@lem7129173 A _95085 _95086)). Qed.
Lemma lem7129175 {A : Type'} (x : type638 A) (_95085 : A -> Prop) (_95086 : A -> Prop) : (term553 A x _95085 _95086) = (term582 A x _95085 _95086).
Proof. exact (TRANS (@lem7129167 A x _95085 _95086) (@lem7129174 A x _95085 _95086)). Qed.
Lemma lem7129178 {A : Type'} (_95085 : A -> Prop) (_95086 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term582 A x _95085 _95086.
Proof. exact (EQ_MP (@lem7129175 A x _95085 _95086) (@lem7128870 A _95085 _95086 x h1)). Qed.
Lemma lem7129179 {A : Type'} (_95085 : A -> Prop) (_95086 : A -> Prop) (x : type638 A) (h1 : term356 A x) : term582 A x _95085 _95086.
Proof. exact (@lem7129178 A _95085 _95086 x h1). Qed.
Lemma lem7129180 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term356 A x) : term583 A x v u.
Proof. exact (@lem7129179 A u (term1 A v u) x h1). Qed.
Lemma lem7129183 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : term189 A v u.
Proof. exact (@lem7129180 A v u x h3 (@lem7129164 A v u x h1 h2 h3)). Qed.
Lemma lem7129184 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term356 A x) : term584 A v u.
Proof. exact (fun h0 : term194 A v u => @lem7129183 A v u x h1 h0 h2). Qed.
Lemma lem7129186 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7129187 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term584 A v u) = (term189 A v u).
Proof. exact (@lem7129186 (term189 A v u)). Qed.
Lemma lem7129188 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term356 A x) : term189 A v u.
Proof. exact (EQ_MP (@lem7129187 A v u) (@lem7129184 A v u x h1 h2)). Qed.
Lemma lem7129191 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7129193 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term194 A v u) = (term585 A v u).
Proof. exact (@lem7129191 (term189 A v u)). Qed.
Lemma lem7129196 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term194 A v u) : term585 A v u.
Proof. exact (EQ_MP (@lem7129193 A v u) (@lem7128834 A v u h1)). Qed.
Lemma lem7129199 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : False.
Proof. exact (@lem7129196 A v u h2 (@lem7129188 A v u x h1 h3)). Qed.
Lemma lem7129200 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : term66.
Proof. exact (fun h0 : ~ False => @lem7129199 A v u x h1 h2 h3). Qed.
Lemma lem7129202 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7129203 : term66 = False.
Proof. exact (@lem7129202 False). Qed.
Lemma lem7129204 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : False.
Proof. exact (EQ_MP (@lem7129203) (@lem7129200 A v u x h1 h2 h3)). Qed.
Lemma lem7129333 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term10 A x' v u.
Proof. exact (proj1 (@lem7128236 A v u f x' h1)). Qed.
Lemma lem7129334 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term586 A x' v u.
Proof. exact (fun h0 : term587 A x' v u => @lem7129333 A v u f x' h1). Qed.
Lemma lem7129336 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7129337 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) : (term586 A x' v u) = (term10 A x' v u).
Proof. exact (@lem7129336 (term10 A x' v u)). Qed.
Lemma lem7129338 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term10 A x' v u.
Proof. exact (EQ_MP (@lem7129337 A x' v u) (@lem7129334 A v u f x' h1)). Qed.
Lemma lem7129341 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term16 A x' u) : term16 A x' u.
Proof. exact (h1). Qed.
Lemma lem7129342 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term16 A x' u) : term588 A x' u.
Proof. exact (fun h0 : @IN A x' u => @lem7129341 A x' u h1). Qed.
Lemma lem7129344 (p : Prop) : (term557 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7129345 {A : Type'} (x' : A) (u : A -> Prop) : (term588 A x' u) = (term16 A x' u).
Proof. exact (@lem7129344 (@IN A x' u)). Qed.
Lemma lem7129346 {A : Type'} (x' : A) (u : A -> Prop) (h1 : term16 A x' u) : term16 A x' u.
Proof. exact (EQ_MP (@lem7129345 A x' u) (@lem7129342 A x' u h1)). Qed.
Lemma lem7129348 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term589 A f x'.
Proof. exact (proj2 (@lem7128234 A v u f x' h1)). Qed.
Lemma lem7129349 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term590 A f x'.
Proof. exact (fun h0 : (f x') = term167 => @lem7129348 A v u f x' h1). Qed.
Lemma lem7129351 (p : Prop) : (term557 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7129352 {A : Type'} (f : A -> real) (x' : A) : (term590 A f x') = (term589 A f x').
Proof. exact (@lem7129351 ((f x') = term167)). Qed.
Lemma lem7129353 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term589 A f x'.
Proof. exact (EQ_MP (@lem7129352 A f x') (@lem7129349 A v u f x' h1)). Qed.
Lemma lem7129355 (b : Prop) (a : Prop) : (a \/ b) = (term561 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7129356 {A : Type'} (u : A -> Prop) (f : A -> real) (_95102 : A) (v : A -> Prop) : (term554 A v u f _95102) = (term591 A u f _95102 v).
Proof. exact (@lem7129355 (term592 A u f _95102) (term16 A _95102 v)). Qed.
Lemma lem7129358 (a : Prop) (b : Prop) : (term593 a b) = (term594 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7129359 {A : Type'} (u : A -> Prop) (f : A -> real) (_95102 : A) : (term595 A u f _95102) = (term596 A u f _95102).
Proof. exact (@lem7129358 (@IN A _95102 u) ((f _95102) = term167)). Qed.
Lemma lem7129360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129361 {A : Type'} (u : A -> Prop) (f : A -> real) (_95102 : A) : (term597 A u f _95102) = (term598 A u f _95102).
Proof. exact (MK_COMB (@lem7129360) (@lem7129359 A u f _95102)). Qed.
Lemma lem7129362 {A : Type'} (_95102 : A) (v : A -> Prop) : (term16 A _95102 v) = (term16 A _95102 v).
Proof. exact (eq_refl (term16 A _95102 v)). Qed.
Lemma lem7129363 {A : Type'} (u : A -> Prop) (f : A -> real) (_95102 : A) (v : A -> Prop) : (term591 A u f _95102 v) = (term599 A u f _95102 v).
Proof. exact (MK_COMB (@lem7129361 A u f _95102) (@lem7129362 A _95102 v)). Qed.
Lemma lem7129364 {A : Type'} (u : A -> Prop) (f : A -> real) (_95102 : A) (v : A -> Prop) : (term554 A v u f _95102) = (term599 A u f _95102 v).
Proof. exact (TRANS (@lem7129356 A u f _95102 v) (@lem7129363 A u f _95102 v)). Qed.
Lemma lem7129366 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term16 A x' u) (h2 : term175 A v u f x') : term596 A u f x'.
Proof. exact (conj (@lem7129346 A x' u h1) (@lem7129353 A v u f x' h2)). Qed.
Lemma lem7129368 {A : Type'} (_95102 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term599 A u f _95102 v.
Proof. exact (EQ_MP (@lem7129364 A u f _95102 v) (@lem7128884 A _95102 v u f h1)). Qed.
Lemma lem7129369 {A : Type'} (_95102 : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term599 A u f _95102 v.
Proof. exact (@lem7129368 A _95102 v u f h1). Qed.
Lemma lem7129370 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term599 A u f x' v.
Proof. exact (@lem7129369 A x' v u f h1). Qed.
Lemma lem7129373 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term16 A x' u) (h3 : term175 A v u f x') : term16 A x' v.
Proof. exact (@lem7129370 A x' v u f h1 (@lem7129366 A v u f x' h2 h3)). Qed.
Lemma lem7129374 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term16 A x' u) (h3 : term175 A v u f x') : term588 A x' v.
Proof. exact (fun h0 : @IN A x' v => @lem7129373 A v u f x' h1 h2 h3). Qed.
Lemma lem7129376 (p : Prop) : (term557 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7129377 {A : Type'} (x' : A) (v : A -> Prop) : (term588 A x' v) = (term16 A x' v).
Proof. exact (@lem7129376 (@IN A x' v)). Qed.
Lemma lem7129378 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term16 A x' u) (h3 : term175 A v u f x') : term16 A x' v.
Proof. exact (EQ_MP (@lem7129377 A x' v) (@lem7129374 A v u f x' h1 h2 h3)). Qed.
Lemma lem7129380 (b : Prop) (a : Prop) : (a \/ b) = (term561 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7129383 {A : Type'} (_95119 : A) (_95117 : A -> Prop) (_95118 : A -> Prop) : (term555 A _95118 _95119 _95117) = (term600 A _95119 _95117 _95118).
Proof. exact (@lem7129380 (@IN A _95119 _95117) (term535 A _95119 _95117 _95118)). Qed.
Lemma lem7129386 {A : Type'} (_95119 : A) (_95117 : A -> Prop) (_95118 : A -> Prop) (h1 : term105 A) : term600 A _95119 _95117 _95118.
Proof. exact (EQ_MP (@lem7129383 A _95119 _95117 _95118) (@lem7128926 A _95118 _95119 _95117 h1)). Qed.
Lemma lem7129387 {A : Type'} (_95119 : A) (_95117 : A -> Prop) (_95118 : A -> Prop) (h1 : term105 A) : term600 A _95119 _95117 _95118.
Proof. exact (@lem7129386 A _95119 _95117 _95118 h1). Qed.
Lemma lem7129388 {A : Type'} (x' : A) (v : A -> Prop) (_95118 : A -> Prop) (h1 : term105 A) : term600 A x' v _95118.
Proof. exact (@lem7129387 A x' v _95118 h1). Qed.
Lemma lem7129391 {A : Type'} (_95118 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term175 A v u f x') : term535 A x' v _95118.
Proof. exact (@lem7129388 A x' v _95118 h2 (@lem7129378 A v u f x' h1 h3 h4)). Qed.
Lemma lem7129392 {A : Type'} (_95118 : A -> Prop) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term175 A v u f x') : term535 A x' v _95118.
Proof. exact (@lem7129391 A _95118 v u f x' h1 h2 h3 h4). Qed.
Lemma lem7129393 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term175 A v u f x') : term535 A x' v u.
Proof. exact (@lem7129392 A u v u f x' h1 h2 h3 h4). Qed.
Lemma lem7129394 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term175 A v u f x') : term601 A x' v u.
Proof. exact (fun h0 : term12 A x' v u => @lem7129393 A v u f x' h1 h2 h3 h4). Qed.
Lemma lem7129396 (p : Prop) : (term557 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7129397 {A : Type'} (x' : A) (v : A -> Prop) (u : A -> Prop) : (term601 A x' v u) = (term535 A x' v u).
Proof. exact (@lem7129396 (term12 A x' v u)). Qed.
Lemma lem7129398 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term175 A v u f x') : term535 A x' v u.
Proof. exact (EQ_MP (@lem7129397 A x' v u) (@lem7129394 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem7129404 (q : Prop) (p : Prop) (r : Prop) : (term74 p q r) = (term74 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7129405 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : (term440 A _95111 _95113 _95112) = (term602 A _95111 _95113 _95112).
Proof. exact (@lem7129404 (@IN A _95113 _95111) (term603 A _95113 _95111 _95112) (@IN A _95113 _95112)). Qed.
Lemma lem7129419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7129420 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term604 A _95111 _95113 _95112) = (term605 A _95113 _95111 _95112).
Proof. exact (@lem7129419 (@IN A _95113 _95112) (term603 A _95113 _95111 _95112)). Qed.
Lemma lem7129426 {A : Type'} (_95113 : A) (_95111 : A -> Prop) : (term5 A _95113 _95111) = (term5 A _95113 _95111).
Proof. exact (eq_refl (term5 A _95113 _95111)). Qed.
Lemma lem7129427 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term602 A _95111 _95113 _95112) = (term606 A _95113 _95111 _95112).
Proof. exact (MK_COMB (@lem7129426 A _95113 _95111) (@lem7129420 A _95113 _95111 _95112)). Qed.
Lemma lem7129438 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term440 A _95111 _95113 _95112) = (term606 A _95113 _95111 _95112).
Proof. exact (TRANS (@lem7129405 A _95111 _95113 _95112) (@lem7129427 A _95113 _95111 _95112)). Qed.
Lemma lem7129439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7129440 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term607 A _95111 _95113 _95112) = (term608 A _95113 _95111 _95112).
Proof. exact (MK_COMB (@lem7129439) (@lem7129438 A _95113 _95111 _95112)). Qed.
Lemma lem7129454 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7129455 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term604 A _95111 _95113 _95112) = (term605 A _95113 _95111 _95112).
Proof. exact (@lem7129454 (@IN A _95113 _95112) (term603 A _95113 _95111 _95112)). Qed.
Lemma lem7129461 {A : Type'} (_95113 : A) (_95111 : A -> Prop) : (term5 A _95113 _95111) = (term5 A _95113 _95111).
Proof. exact (eq_refl (term5 A _95113 _95111)). Qed.
Lemma lem7129462 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term602 A _95111 _95113 _95112) = (term606 A _95113 _95111 _95112).
Proof. exact (MK_COMB (@lem7129461 A _95113 _95111) (@lem7129455 A _95113 _95111 _95112)). Qed.
Lemma lem7129473 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : ((term440 A _95111 _95113 _95112) = (term602 A _95111 _95113 _95112)) = ((term606 A _95113 _95111 _95112) = (term606 A _95113 _95111 _95112)).
Proof. exact (MK_COMB (@lem7129440 A _95113 _95111 _95112) (@lem7129462 A _95113 _95111 _95112)). Qed.
Lemma lem7129475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7129476 (x : Prop) : (x = x) = True.
Proof. exact (@lem7129475 Prop x). Qed.
Lemma lem7129477 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : ((term606 A _95113 _95111 _95112) = (term606 A _95113 _95111 _95112)) = True.
Proof. exact (@lem7129476 (term606 A _95113 _95111 _95112)). Qed.
Lemma lem7129478 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : ((term440 A _95111 _95113 _95112) = (term602 A _95111 _95113 _95112)) = True.
Proof. exact (TRANS (@lem7129473 A _95113 _95111 _95112) (@lem7129477 A _95113 _95111 _95112)). Qed.
Lemma lem7129479 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : True = ((term440 A _95111 _95113 _95112) = (term602 A _95111 _95113 _95112)).
Proof. exact (SYM (@lem7129478 A _95111 _95113 _95112)). Qed.
Lemma lem7129480 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : (term440 A _95111 _95113 _95112) = (term602 A _95111 _95113 _95112).
Proof. exact (EQ_MP (@lem7129479 A _95111 _95113 _95112) (@lem0)). Qed.
Lemma lem7129481 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) (h1 : term104 A) : term602 A _95111 _95113 _95112.
Proof. exact (EQ_MP (@lem7129480 A _95111 _95113 _95112) (@lem7128904 A _95111 _95113 _95112 h1)). Qed.
Lemma lem7129483 (b : Prop) (a : Prop) : (a \/ b) = (term561 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7129484 {A : Type'} (_95112 : A -> Prop) (_95113 : A) (_95111 : A -> Prop) : (term602 A _95111 _95113 _95112) = (term609 A _95112 _95113 _95111).
Proof. exact (@lem7129483 (term604 A _95111 _95113 _95112) (@IN A _95113 _95111)). Qed.
Lemma lem7129486 (a : Prop) (b : Prop) : (term593 a b) = (term594 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7129487 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : (term610 A _95111 _95113 _95112) = (term611 A _95111 _95113 _95112).
Proof. exact (@lem7129486 (term603 A _95113 _95111 _95112) (@IN A _95113 _95112)). Qed.
Lemma lem7129489 (a : Prop) : (term30 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7129490 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term612 A _95113 _95111 _95112) = (term3 A _95113 _95111 _95112).
Proof. exact (@lem7129489 (term3 A _95113 _95111 _95112)). Qed.
Lemma lem7129491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7129492 {A : Type'} (_95113 : A) (_95111 : A -> Prop) (_95112 : A -> Prop) : (term613 A _95113 _95111 _95112) = (term614 A _95113 _95111 _95112).
Proof. exact (MK_COMB (@lem7129491) (@lem7129490 A _95113 _95111 _95112)). Qed.
Lemma lem7129493 {A : Type'} (_95113 : A) (_95112 : A -> Prop) : (term16 A _95113 _95112) = (term16 A _95113 _95112).
Proof. exact (eq_refl (term16 A _95113 _95112)). Qed.
Lemma lem7129494 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : (term611 A _95111 _95113 _95112) = (term615 A _95111 _95113 _95112).
Proof. exact (MK_COMB (@lem7129492 A _95113 _95111 _95112) (@lem7129493 A _95113 _95112)). Qed.
Lemma lem7129495 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : (term610 A _95111 _95113 _95112) = (term615 A _95111 _95113 _95112).
Proof. exact (TRANS (@lem7129487 A _95111 _95113 _95112) (@lem7129494 A _95111 _95113 _95112)). Qed.
Lemma lem7129496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129497 {A : Type'} (_95111 : A -> Prop) (_95113 : A) (_95112 : A -> Prop) : (term616 A _95111 _95113 _95112) = (term617 A _95111 _95113 _95112).
Proof. exact (MK_COMB (@lem7129496) (@lem7129495 A _95111 _95113 _95112)). Qed.
Lemma lem7129498 {A : Type'} (_95113 : A) (_95111 : A -> Prop) : (@IN A _95113 _95111) = (@IN A _95113 _95111).
Proof. exact (eq_refl (@IN A _95113 _95111)). Qed.
Lemma lem7129499 {A : Type'} (_95112 : A -> Prop) (_95113 : A) (_95111 : A -> Prop) : (term609 A _95112 _95113 _95111) = (term618 A _95112 _95113 _95111).
Proof. exact (MK_COMB (@lem7129497 A _95111 _95113 _95112) (@lem7129498 A _95113 _95111)). Qed.
Lemma lem7129500 {A : Type'} (_95112 : A -> Prop) (_95113 : A) (_95111 : A -> Prop) : (term602 A _95111 _95113 _95112) = (term618 A _95112 _95113 _95111).
Proof. exact (TRANS (@lem7129484 A _95112 _95113 _95111) (@lem7129499 A _95112 _95113 _95111)). Qed.
Lemma lem7129502 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term16 A x' u) (h4 : term175 A v u f x') : term619 A x' v u.
Proof. exact (conj (@lem7129338 A v u f x' h4) (@lem7129398 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem7129504 {A : Type'} (_95112 : A -> Prop) (_95113 : A) (_95111 : A -> Prop) (h1 : term104 A) : term618 A _95112 _95113 _95111.
Proof. exact (EQ_MP (@lem7129500 A _95112 _95113 _95111) (@lem7129481 A _95111 _95113 _95112 h1)). Qed.
Lemma lem7129505 {A : Type'} (_95112 : A -> Prop) (_95113 : A) (_95111 : A -> Prop) (h1 : term104 A) : term618 A _95112 _95113 _95111.
Proof. exact (@lem7129504 A _95112 _95113 _95111 h1). Qed.
Lemma lem7129506 {A : Type'} (v : A -> Prop) (x' : A) (u : A -> Prop) (h1 : term104 A) : term620 A v x' u.
Proof. exact (@lem7129505 A (@DIFF A v u) x' u h1). Qed.
Lemma lem7129509 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term16 A x' u) (h5 : term175 A v u f x') : @IN A x' u.
Proof. exact (@lem7129506 A v x' u h3 (@lem7129502 A v u f x' h1 h2 h4 h5)). Qed.
Lemma lem7129510 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term175 A v u f x') : term621 A x' u.
Proof. exact (fun h0 : term16 A x' u => @lem7129509 A v u f x' h1 h2 h3 h0 h4). Qed.
Lemma lem7129512 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7129513 {A : Type'} (x' : A) (u : A -> Prop) : (term621 A x' u) = (@IN A x' u).
Proof. exact (@lem7129512 (@IN A x' u)). Qed.
Lemma lem7129514 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term175 A v u f x') : @IN A x' u.
Proof. exact (EQ_MP (@lem7129513 A x' u) (@lem7129510 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem7129517 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7129519 {A : Type'} (x' : A) (u : A -> Prop) : (term16 A x' u) = (term622 A x' u).
Proof. exact (@lem7129517 (@IN A x' u)). Qed.
Lemma lem7129522 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term175 A v u f x') : term622 A x' u.
Proof. exact (EQ_MP (@lem7129519 A x' u) (@lem7128920 A v u f x' h1)). Qed.
Lemma lem7129525 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term175 A v u f x') : False.
Proof. exact (@lem7129522 A v u f x' h4 (@lem7129514 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem7129526 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term175 A v u f x') : term66.
Proof. exact (fun h0 : ~ False => @lem7129525 A v u f x' h1 h2 h3 h4). Qed.
Lemma lem7129528 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7129529 : term66 = False.
Proof. exact (@lem7129528 False). Qed.
Lemma lem7129530 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term175 A v u f x') : False.
Proof. exact (EQ_MP (@lem7129529) (@lem7129526 A v u f x' h1 h2 h3 h4)). Qed.
Lemma lem7129531 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : (term194 A v u) = False.
Proof. exact (prop_ext (fun h4 : term194 A v u => @lem7129204 A v u x h1 h2 h3) (fun h4 : False => @lem7128834 A v u h2)). Qed.
Lemma lem7129532 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : False.
Proof. exact (EQ_MP (@lem7129531 A v u x h1 h2 h3) (@lem7128834 A v u h2)). Qed.
Lemma lem7129533 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : (term194 A v u) = False.
Proof. exact (prop_ext (fun h4 : term194 A v u => @lem7129532 A v u x h1 h2 h3) (fun h4 : False => @lem7128449 A v u h2)). Qed.
Lemma lem7129534 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : False.
Proof. exact (EQ_MP (@lem7129533 A v u x h1 h2 h3) (@lem7128449 A v u h2)). Qed.
Lemma lem7129535 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : (term194 A v u) = False.
Proof. exact (prop_ext (fun h4 : term194 A v u => @lem7129534 A v u x h1 h2 h3) (fun h4 : False => @lem7128449 A v u h2)). Qed.
Lemma lem7129536 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : type638 A) (h1 : term104 A) (h2 : term194 A v u) (h3 : term356 A x) : False.
Proof. exact (EQ_MP (@lem7129535 A v u x h1 h2 h3) (@lem7128449 A v u h2)). Qed.
Lemma lem7129537 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term356 A x) (h5 : term201 A v u f x') : False.
Proof. exact (or_elim (@lem7128226 A v u f x' h5) (fun h0 : term194 A v u => @lem7129536 A v u x h3 h0 h4) (fun h0 : term175 A v u f x' => @lem7129530 A v u f x' h1 h2 h3 h0)). Qed.
Lemma lem7129538 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term356 A x) (h5 : term201 A v u f x') : (term201 A v u f x') = False.
Proof. exact (prop_ext (fun h6 : term201 A v u f x' => @lem7129537 A x v u f x' h1 h2 h3 h4 h5) (fun h6 : False => @lem7128226 A v u f x' h5)). Qed.
Lemma lem7129539 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term356 A x) (h5 : term201 A v u f x') : False.
Proof. exact (EQ_MP (@lem7129538 A x v u f x' h1 h2 h3 h4 h5) (@lem7128226 A v u f x' h5)). Qed.
Lemma lem7129540 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term356 A x) (h5 : term201 A v u f x') : (term356 A x) = False.
Proof. exact (prop_ext (fun h6 : term356 A x => @lem7129539 A x v u f x' h1 h2 h3 h4 h5) (fun h6 : False => @lem7128168 A x h4)). Qed.
Lemma lem7129541 {A : Type'} (x : type638 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x' : A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term356 A x) (h5 : term201 A v u f x') : False.
Proof. exact (EQ_MP (@lem7129540 A x v u f x' h1 h2 h3 h4 h5) (@lem7128168 A x h4)). Qed.
Lemma lem7129542 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : type638 A) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term103 A v u f) (h5 : term356 A x) : False.
Proof. exact (ex_elim (@lem7126382 A v u f h4) (fun x' : A => fun h0 : term203 A v u f x' => @lem7129541 A x v u f x' h1 h2 h3 h5 h0)). Qed.
Lemma lem7129543 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term104 A) (h4 : term106 A) (h5 : term103 A v u f) : False.
Proof. exact (ex_elim (@lem7127002 A h4) (fun x : type638 A => fun h0 : term358 A x => @lem7129542 A v u f x h1 h2 h3 h5 h0)). Qed.
Lemma lem7129544 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term106 A) (h4 : term103 A v u f) : term111 A.
Proof. exact (fun h0 : term104 A => @lem7129543 A v u f h1 h2 h0 h3 h4). Qed.
Lemma lem7129545 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (@lem69 (term104 A)). Qed.
Lemma lem7129546 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : term105 A) (h3 : term106 A) (h4 : term103 A v u f) : term112 A.
Proof. exact (EQ_MP (@lem7129545 A) (@lem7129544 A v u f h1 h2 h3 h4)). Qed.
Lemma lem7129547 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : term106 A) (h3 : term103 A v u f) : term115 A.
Proof. exact (fun h0 : term105 A => @lem7129546 A v u f h1 h0 h2 h3). Qed.
Lemma lem7129548 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : term103 A v u f) : term118 A.
Proof. exact (fun h0 : term106 A => @lem7129547 A v u f h1 h0 h2). Qed.
Lemma lem7129549 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) : term121 A v u f.
Proof. exact (fun h0 : term103 A v u f => @lem7129548 A v u f h1 h0). Qed.
Lemma lem7129550 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term124 A v u f.
Proof. exact (fun h0 : term93 A v u f => @lem7129549 A v u f h0). Qed.
Lemma lem7129551 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term126 A v u f.
Proof. exact (fun h0 : @FINITE A u => @lem7129550 A v u f). Qed.
Lemma lem7129556 {A : Type'} (u : A -> Prop) (f : A -> real) : term130 A u f.
Proof. exact (fun v : A -> Prop => @lem7129551 A v u f). Qed.
Lemma lem7129561 {A : Type'} (f : A -> real) : term134 A f.
Proof. exact (fun u : A -> Prop => @lem7129556 A u f). Qed.
Lemma lem7129566 {A : Type'} : term138 A.
Proof. exact (fun f : A -> real => @lem7129561 A f). Qed.
Lemma lem7129567 {A : Type'} : term137 A.
Proof. exact (EQ_MP (@lem7126200 A) (@lem7129566 A)). Qed.
Lemma lem7129568 {A : Type'} (f : A -> real) : term623 A f.
Proof. exact (@lem7129567 A f). Qed.
Lemma lem7129569 {A : Type'} (f : A -> real) : (term623 A f) = (term133 A f).
Proof. exact (eq_refl (term623 A f)). Qed.
Lemma lem7129570 {A : Type'} (f : A -> real) : term133 A f.
Proof. exact (EQ_MP (@lem7129569 A f) (@lem7129568 A f)). Qed.
Lemma lem7129571 {A : Type'} (f : A -> real) (u : A -> Prop) : term624 A f u.
Proof. exact (@lem7129570 A f u). Qed.
Lemma lem7129572 {A : Type'} (u : A -> Prop) (f : A -> real) : (term624 A f u) = (term129 A u f).
Proof. exact (eq_refl (term624 A f u)). Qed.
Lemma lem7129573 {A : Type'} (u : A -> Prop) (f : A -> real) : term129 A u f.
Proof. exact (EQ_MP (@lem7129572 A u f) (@lem7129571 A f u)). Qed.
Lemma lem7129574 {A : Type'} (u : A -> Prop) (f : A -> real) (v : A -> Prop) : term625 A u f v.
Proof. exact (@lem7129573 A u f v). Qed.
Lemma lem7129575 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term625 A u f v) = (term107 A v u f).
Proof. exact (eq_refl (term625 A u f v)). Qed.
Lemma lem7129576 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term107 A v u f.
Proof. exact (EQ_MP (@lem7129575 A v u f) (@lem7129574 A u f v)). Qed.
Lemma lem7129578 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term107 A v u f.
Proof. exact (@lem7125839 A v u f (@lem7129576 A v u f)). Qed.
Lemma lem7129579 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : @FINITE A u) : term123 A v u f.
Proof. exact (@lem7129578 A v u f (@lem7125794 A u h1)). Qed.
Lemma lem7129580 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : term120 A v u f.
Proof. exact (@lem7129579 A v f u h2 (@lem7125793 A v u f h1)). Qed.
Lemma lem7129581 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : term117 A.
Proof. exact (@lem7129580 A v f u h1 h2 (@lem7125817 A v u f h3)). Qed.
Lemma lem7129582 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : term114 A.
Proof. exact (@lem7129581 A v u f h1 h2 h3 (@lem7125822 A)). Qed.
Lemma lem7129583 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : term111 A.
Proof. exact (@lem7129582 A v u f h1 h2 h3 (@lem7125820 A)). Qed.
Lemma lem7129584 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : False.
Proof. exact (@lem7129583 A v u f h1 h2 h3 (@lem7125818 A)). Qed.
Lemma lem7129585 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : (term103 A v u f) = False.
Proof. exact (prop_ext (fun h4 : term103 A v u f => @lem7129584 A v u f h1 h2 h3) (fun h4 : False => @lem7125817 A v u f h3)). Qed.
Lemma lem7129586 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term93 A v u f) (h2 : @FINITE A u) (h3 : term103 A v u f) : False.
Proof. exact (EQ_MP (@lem7129585 A v u f h1 h2 h3) (@lem7125817 A v u f h3)). Qed.
Lemma lem7129587 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : term102 A v u f.
Proof. exact (fun h0 : term103 A v u f => @lem7129586 A v u f h1 h2 h0). Qed.
Lemma lem7129588 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : term101 A v u f.
Proof. exact (EQ_MP (@lem7125816 A v u f) (@lem7129587 A v f u h1 h2)). Qed.
Lemma lem7129589 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term97 A v u f) = (@sum A u f).
Proof. exact (@lem7125812 A v u f (@lem7129588 A v f u h1 h2)). Qed.
Lemma lem7129590 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term96 A u v f) = (@sum A u f).
Proof. exact (EQ_MP (@lem7125808 A v u f) (@lem7129589 A v f u h1 h2)). Qed.
Lemma lem7129591 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term92 A v u f) : term93 A v u f.
Proof. exact (proj2 (@lem7125792 A v u f h1)). Qed.
Lemma lem7129592 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term92 A v u f) : @FINITE A u.
Proof. exact (proj1 (@lem7125792 A v u f h1)). Qed.
Lemma lem7129593 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term93 A v u f) = ((term96 A u v f) = (@sum A u f)).
Proof. exact (prop_ext (fun h3 : term93 A v u f => @lem7129590 A v f u h1 h2) (fun h3 : (term96 A u v f) = (@sum A u f) => @lem7125793 A v u f h1)). Qed.
Lemma lem7129594 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term96 A u v f) = (@sum A u f).
Proof. exact (EQ_MP (@lem7129593 A v f u h1 h2) (@lem7125793 A v u f h1)). Qed.
Lemma lem7129595 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (@FINITE A u) = ((term96 A u v f) = (@sum A u f)).
Proof. exact (prop_ext (fun h3 : @FINITE A u => @lem7129594 A v f u h1 h2) (fun h3 : (term96 A u v f) = (@sum A u f) => @lem7125794 A u h2)). Qed.
Lemma lem7129596 {A : Type'} (v : A -> Prop) (f : A -> real) (u : A -> Prop) (h1 : term93 A v u f) (h2 : @FINITE A u) : (term96 A u v f) = (@sum A u f).
Proof. exact (EQ_MP (@lem7129595 A v f u h1 h2) (@lem7125794 A u h2)). Qed.
Lemma lem7129597 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term92 A v u f) : (term93 A v u f) = ((term96 A u v f) = (@sum A u f)).
Proof. exact (prop_ext (fun h3 : term93 A v u f => @lem7129596 A v f u h3 h1) (fun h3 : (term96 A u v f) = (@sum A u f) => @lem7129591 A v u f h2)). Qed.
Lemma lem7129598 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term92 A v u f) : (term96 A u v f) = (@sum A u f).
Proof. exact (EQ_MP (@lem7129597 A v u f h1 h2) (@lem7129591 A v u f h2)). Qed.
Lemma lem7129599 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term92 A v u f) : (@FINITE A u) = ((term96 A u v f) = (@sum A u f)).
Proof. exact (prop_ext (fun h2 : @FINITE A u => @lem7129598 A v u f h2 h1) (fun h2 : (term96 A u v f) = (@sum A u f) => @lem7129592 A v u f h1)). Qed.
Lemma lem7129600 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term92 A v u f) : (term96 A u v f) = (@sum A u f).
Proof. exact (EQ_MP (@lem7129599 A v u f h1) (@lem7129592 A v u f h1)). Qed.
Lemma lem7129601 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term626 A v u f.
Proof. exact (fun h0 : term92 A v u f => @lem7129600 A v u f h0). Qed.
Lemma lem7129606 {A : Type'} (u : A -> Prop) (f : A -> real) : term627 A u f.
Proof. exact (fun v : A -> Prop => @lem7129601 A v u f). Qed.
Lemma lem7129611 {A : Type'} (f : A -> real) : term628 A f.
Proof. exact (fun u : A -> Prop => @lem7129606 A u f). Qed.
Lemma lem7129616 {A : Type'} : term629 A.
Proof. exact (fun f : A -> real => @lem7129611 A f). Qed.
