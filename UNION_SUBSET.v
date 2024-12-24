Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3237039 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3237040 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (@SUBSET _84841 s t) = (term0 _84841 s t).
Proof. exact (@lem3237039 _84841 s t). Qed.
Lemma lem3237041 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term1 _84841 s t u) = (term2 _84841 s t u).
Proof. exact (@lem3237040 _84841 (@UNION _84841 s t) u). Qed.
Lemma lem3237048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3237049 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term3 _84841 s t u) = (term4 _84841 s t u).
Proof. exact (MK_COMB (@lem3237048) (@lem3237041 _84841 s t u)). Qed.
Lemma lem3237053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3237054 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (@SUBSET _84841 s t) = (term0 _84841 s t).
Proof. exact (@lem3237053 _84841 s t). Qed.
Lemma lem3237055 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (@SUBSET _84841 s u) = (term0 _84841 s u).
Proof. exact (@lem3237054 _84841 s u). Qed.
Lemma lem3237062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237063 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term5 _84841 s u) = (term6 _84841 s u).
Proof. exact (MK_COMB (@lem3237062) (@lem3237055 _84841 s u)). Qed.
Lemma lem3237065 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3237066 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (@SUBSET _84841 s t) = (term0 _84841 s t).
Proof. exact (@lem3237065 _84841 s t). Qed.
Lemma lem3237067 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (@SUBSET _84841 t u) = (term0 _84841 t u).
Proof. exact (@lem3237066 _84841 t u). Qed.
Lemma lem3237074 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term7 _84841 s t u) = (term8 _84841 s t u).
Proof. exact (MK_COMB (@lem3237063 _84841 s u) (@lem3237067 _84841 t u)). Qed.
Lemma lem3237077 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term1 _84841 s t u) = (term7 _84841 s t u)) = ((term2 _84841 s t u) = (term8 _84841 s t u)).
Proof. exact (MK_COMB (@lem3237049 _84841 s t u) (@lem3237074 _84841 s t u)). Qed.
Lemma lem3237082 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (term9 _84841 s t) = (term10 _84841 s t).
Proof. exact (fun_ext (fun u : _84841 -> Prop => @lem3237077 _84841 s t u)). Qed.
Lemma lem3237083 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237084 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (term11 _84841 s t) = (term12 _84841 s t).
Proof. exact (MK_COMB (@lem3237083 _84841) (@lem3237082 _84841 s t)). Qed.
Lemma lem3237089 {_84841 : Type'} (s : _84841 -> Prop) : (term13 _84841 s) = (term14 _84841 s).
Proof. exact (fun_ext (fun t : _84841 -> Prop => @lem3237084 _84841 s t)). Qed.
Lemma lem3237090 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237091 {_84841 : Type'} (s : _84841 -> Prop) : (term15 _84841 s) = (term16 _84841 s).
Proof. exact (MK_COMB (@lem3237090 _84841) (@lem3237089 _84841 s)). Qed.
Lemma lem3237096 {_84841 : Type'} : (term17 _84841) = (term18 _84841).
Proof. exact (fun_ext (fun s : _84841 -> Prop => @lem3237091 _84841 s)). Qed.
Lemma lem3237097 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237098 {_84841 : Type'} : (term19 _84841) = (term20 _84841).
Proof. exact (MK_COMB (@lem3237097 _84841) (@lem3237096 _84841)). Qed.
Lemma lem3237103 {_84841 : Type'} : (term20 _84841) = (term19 _84841).
Proof. exact (SYM (@lem3237098 _84841)). Qed.
Lemma lem3237125 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3237126 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) (t : _84841 -> Prop) : (term21 _84841 x s t) = (term22 _84841 s x t).
Proof. exact (@lem3237125 _84841 s x t). Qed.
Lemma lem3237130 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3237131 {_84841 : Type'} (P : _84841 -> Prop) (x : _84841) : (@IN _84841 x P) = (P x).
Proof. exact (@lem3237130 _84841 P x). Qed.
Lemma lem3237132 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) : (@IN _84841 x s) = (s x).
Proof. exact (@lem3237131 _84841 s x). Qed.
Lemma lem3237133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237134 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) : (term23 _84841 x s) = (term24 _84841 s x).
Proof. exact (MK_COMB (@lem3237133) (@lem3237132 _84841 s x)). Qed.
Lemma lem3237136 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3237137 {_84841 : Type'} (P : _84841 -> Prop) (x : _84841) : (@IN _84841 x P) = (P x).
Proof. exact (@lem3237136 _84841 P x). Qed.
Lemma lem3237138 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) : (@IN _84841 x t) = (t x).
Proof. exact (@lem3237137 _84841 t x). Qed.
Lemma lem3237139 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (x : _84841) : (term22 _84841 s x t) = (term25 _84841 s t x).
Proof. exact (MK_COMB (@lem3237134 _84841 s x) (@lem3237138 _84841 t x)). Qed.
Lemma lem3237142 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (x : _84841) : (term21 _84841 x s t) = (term25 _84841 s t x).
Proof. exact (TRANS (@lem3237126 _84841 s x t) (@lem3237139 _84841 s t x)). Qed.
Lemma lem3237143 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3237144 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (x : _84841) : (term26 _84841 x s t) = (term27 _84841 s t x).
Proof. exact (MK_COMB (@lem3237143) (@lem3237142 _84841 s t x)). Qed.
Lemma lem3237146 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3237147 {_84841 : Type'} (P : _84841 -> Prop) (x : _84841) : (@IN _84841 x P) = (P x).
Proof. exact (@lem3237146 _84841 P x). Qed.
Lemma lem3237148 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (@IN _84841 x u) = (u x).
Proof. exact (@lem3237147 _84841 u x). Qed.
Lemma lem3237149 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term28 _84841 s t x u) = (term29 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237144 _84841 s t x) (@lem3237148 _84841 u x)). Qed.
Lemma lem3237152 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term30 _84841 s t u) = (term31 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237149 _84841 s t u x)). Qed.
Lemma lem3237153 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237154 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term2 _84841 s t u) = (term32 _84841 s t u).
Proof. exact (MK_COMB (@lem3237153 _84841) (@lem3237152 _84841 s t u)). Qed.
Lemma lem3237159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3237160 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term4 _84841 s t u) = (term33 _84841 s t u).
Proof. exact (MK_COMB (@lem3237159) (@lem3237154 _84841 s t u)). Qed.
Lemma lem3237170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3237171 {_84841 : Type'} (P : _84841 -> Prop) (x : _84841) : (@IN _84841 x P) = (P x).
Proof. exact (@lem3237170 _84841 P x). Qed.
Lemma lem3237172 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) : (@IN _84841 x s) = (s x).
Proof. exact (@lem3237171 _84841 s x). Qed.
Lemma lem3237173 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3237174 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) : (term34 _84841 x s) = (term35 _84841 s x).
Proof. exact (MK_COMB (@lem3237173) (@lem3237172 _84841 s x)). Qed.
Lemma lem3237176 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3237177 {_84841 : Type'} (P : _84841 -> Prop) (x : _84841) : (@IN _84841 x P) = (P x).
Proof. exact (@lem3237176 _84841 P x). Qed.
Lemma lem3237178 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (@IN _84841 x u) = (u x).
Proof. exact (@lem3237177 _84841 u x). Qed.
Lemma lem3237179 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term36 _84841 s x u) = (term37 _84841 s u x).
Proof. exact (MK_COMB (@lem3237174 _84841 s x) (@lem3237178 _84841 u x)). Qed.
Lemma lem3237182 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term38 _84841 s u) = (term39 _84841 s u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237179 _84841 s u x)). Qed.
Lemma lem3237183 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237184 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term0 _84841 s u) = (term40 _84841 s u).
Proof. exact (MK_COMB (@lem3237183 _84841) (@lem3237182 _84841 s u)). Qed.
Lemma lem3237189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237190 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term6 _84841 s u) = (term41 _84841 s u).
Proof. exact (MK_COMB (@lem3237189) (@lem3237184 _84841 s u)). Qed.
Lemma lem3237198 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3237199 {_84841 : Type'} (P : _84841 -> Prop) (x : _84841) : (@IN _84841 x P) = (P x).
Proof. exact (@lem3237198 _84841 P x). Qed.
Lemma lem3237200 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) : (@IN _84841 x t) = (t x).
Proof. exact (@lem3237199 _84841 t x). Qed.
Lemma lem3237201 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3237202 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) : (term34 _84841 x t) = (term35 _84841 t x).
Proof. exact (MK_COMB (@lem3237201) (@lem3237200 _84841 t x)). Qed.
Lemma lem3237204 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3237205 {_84841 : Type'} (P : _84841 -> Prop) (x : _84841) : (@IN _84841 x P) = (P x).
Proof. exact (@lem3237204 _84841 P x). Qed.
Lemma lem3237206 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (@IN _84841 x u) = (u x).
Proof. exact (@lem3237205 _84841 u x). Qed.
Lemma lem3237207 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term36 _84841 t x u) = (term37 _84841 t u x).
Proof. exact (MK_COMB (@lem3237202 _84841 t x) (@lem3237206 _84841 u x)). Qed.
Lemma lem3237210 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term38 _84841 t u) = (term39 _84841 t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237207 _84841 t u x)). Qed.
Lemma lem3237211 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237212 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term0 _84841 t u) = (term40 _84841 t u).
Proof. exact (MK_COMB (@lem3237211 _84841) (@lem3237210 _84841 t u)). Qed.
Lemma lem3237217 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term8 _84841 s t u) = (term42 _84841 s t u).
Proof. exact (MK_COMB (@lem3237190 _84841 s u) (@lem3237212 _84841 t u)). Qed.
Lemma lem3237220 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term2 _84841 s t u) = (term8 _84841 s t u)) = ((term32 _84841 s t u) = (term42 _84841 s t u)).
Proof. exact (MK_COMB (@lem3237160 _84841 s t u) (@lem3237217 _84841 s t u)). Qed.
Lemma lem3237223 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (term10 _84841 s t) = (term43 _84841 s t).
Proof. exact (fun_ext (fun u : _84841 -> Prop => @lem3237220 _84841 s t u)). Qed.
Lemma lem3237224 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237225 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (term12 _84841 s t) = (term44 _84841 s t).
Proof. exact (MK_COMB (@lem3237224 _84841) (@lem3237223 _84841 s t)). Qed.
Lemma lem3237230 {_84841 : Type'} (s : _84841 -> Prop) : (term14 _84841 s) = (term45 _84841 s).
Proof. exact (fun_ext (fun t : _84841 -> Prop => @lem3237225 _84841 s t)). Qed.
Lemma lem3237231 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237232 {_84841 : Type'} (s : _84841 -> Prop) : (term16 _84841 s) = (term46 _84841 s).
Proof. exact (MK_COMB (@lem3237231 _84841) (@lem3237230 _84841 s)). Qed.
Lemma lem3237237 {_84841 : Type'} : (term18 _84841) = (term47 _84841).
Proof. exact (fun_ext (fun s : _84841 -> Prop => @lem3237232 _84841 s)). Qed.
Lemma lem3237238 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237239 {_84841 : Type'} : (term20 _84841) = (term48 _84841).
Proof. exact (MK_COMB (@lem3237238 _84841) (@lem3237237 _84841)). Qed.
Lemma lem3237244 {_84841 : Type'} : (term48 _84841) = (term20 _84841).
Proof. exact (SYM (@lem3237239 _84841)). Qed.
Lemma lem3237246 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3237247 {_84841 : Type'} : (term48 _84841) = (term50 _84841).
Proof. exact (@lem3237246 (term48 _84841)). Qed.
Lemma lem3237248 {_84841 : Type'} : (term50 _84841) = (term48 _84841).
Proof. exact (SYM (@lem3237247 _84841)). Qed.
Lemma lem3237249 {_84841 : Type'} (h1 : term51 _84841) : term51 _84841.
Proof. exact (h1). Qed.
Lemma lem3237252 {_84841 : Type'} (h1 : term50 _84841) : term50 _84841.
Proof. exact (h1). Qed.
Lemma lem3237253 {_84841 : Type'} : term52 _84841.
Proof. exact (fun h0 : term50 _84841 => @lem3237252 _84841 h0). Qed.
Lemma lem3237254 {_84841 : Type'} (h1 : term52 _84841) : term52 _84841.
Proof. exact (h1). Qed.
Lemma lem3237255 {_84841 : Type'} (h1 : term50 _84841) : term50 _84841.
Proof. exact (h1). Qed.
Lemma lem3237256 {_84841 : Type'} (h1 : term50 _84841) (h2 : term52 _84841) : term50 _84841.
Proof. exact (@lem3237254 _84841 h2 (@lem3237255 _84841 h1)). Qed.
Lemma lem3237257 {_84841 : Type'} (h1 : term50 _84841) : term53 _84841.
Proof. exact (fun h0 : term52 _84841 => @lem3237256 _84841 h1 h0). Qed.
Lemma lem3237258 {_84841 : Type'} (h1 : term52 _84841) : term52 _84841.
Proof. exact (h1). Qed.
Lemma lem3237259 {_84841 : Type'} (h1 : term50 _84841) (h2 : term52 _84841) : term50 _84841.
Proof. exact (@lem3237257 _84841 h1 (@lem3237258 _84841 h2)). Qed.
Lemma lem3237260 {_84841 : Type'} (h1 : term52 _84841) : term52 _84841.
Proof. exact (fun h0 : term50 _84841 => @lem3237259 _84841 h0 h1). Qed.
Lemma lem3237261 {_84841 : Type'} : term54 _84841.
Proof. exact (fun h0 : term52 _84841 => @lem3237260 _84841 h0). Qed.
Lemma lem3237264 {_84841 : Type'} : term52 _84841.
Proof. exact (@lem3237261 _84841 (@lem3237253 _84841)). Qed.
Lemma lem3237265 {_84841 : Type'} : term52 _84841.
Proof. exact (@lem3237264 _84841). Qed.
Lemma lem3237267 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3237268 {_84841 : Type'} : (term50 _84841) = (term55 _84841).
Proof. exact (@lem3237267 (term51 _84841)). Qed.
Lemma lem3237270 (t : Prop) : (term56 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3237271 {_84841 : Type'} : (term55 _84841) = (term48 _84841).
Proof. exact (@lem3237270 (term48 _84841)). Qed.
Lemma lem3237310 {_84841 : Type'} : (term50 _84841) = (term48 _84841).
Proof. exact (TRANS (@lem3237268 _84841) (@lem3237271 _84841)). Qed.
Lemma lem3237315 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term37 _84841 t u x) = (term37 _84841 t u x).
Proof. exact (eq_refl (term37 _84841 t u x)). Qed.
Lemma lem3237316 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term39 _84841 t u) = (term39 _84841 t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237315 _84841 t u x)). Qed.
Lemma lem3237317 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237318 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term40 _84841 t u) = (term40 _84841 t u).
Proof. exact (MK_COMB (@lem3237317 _84841) (@lem3237316 _84841 t u)). Qed.
Lemma lem3237323 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term37 _84841 s u x) = (term37 _84841 s u x).
Proof. exact (eq_refl (term37 _84841 s u x)). Qed.
Lemma lem3237324 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term39 _84841 s u) = (term39 _84841 s u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237323 _84841 s u x)). Qed.
Lemma lem3237325 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237326 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term40 _84841 s u) = (term40 _84841 s u).
Proof. exact (MK_COMB (@lem3237325 _84841) (@lem3237324 _84841 s u)). Qed.
Lemma lem3237327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237328 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term41 _84841 s u) = (term41 _84841 s u).
Proof. exact (MK_COMB (@lem3237327) (@lem3237326 _84841 s u)). Qed.
Lemma lem3237329 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term42 _84841 s t u) = (term42 _84841 s t u).
Proof. exact (MK_COMB (@lem3237328 _84841 s u) (@lem3237318 _84841 t u)). Qed.
Lemma lem3237338 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term29 _84841 s t u x) = (term29 _84841 s t u x).
Proof. exact (eq_refl (term29 _84841 s t u x)). Qed.
Lemma lem3237339 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term31 _84841 s t u) = (term31 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237338 _84841 s t u x)). Qed.
Lemma lem3237340 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237341 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term32 _84841 s t u) = (term32 _84841 s t u).
Proof. exact (MK_COMB (@lem3237340 _84841) (@lem3237339 _84841 s t u)). Qed.
Lemma lem3237342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3237343 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term33 _84841 s t u) = (term33 _84841 s t u).
Proof. exact (MK_COMB (@lem3237342) (@lem3237341 _84841 s t u)). Qed.
Lemma lem3237344 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term32 _84841 s t u) = (term42 _84841 s t u)) = ((term32 _84841 s t u) = (term42 _84841 s t u)).
Proof. exact (MK_COMB (@lem3237343 _84841 s t u) (@lem3237329 _84841 s t u)). Qed.
Lemma lem3237345 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (term43 _84841 s t) = (term43 _84841 s t).
Proof. exact (fun_ext (fun u : _84841 -> Prop => @lem3237344 _84841 s t u)). Qed.
Lemma lem3237346 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237347 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (term44 _84841 s t) = (term44 _84841 s t).
Proof. exact (MK_COMB (@lem3237346 _84841) (@lem3237345 _84841 s t)). Qed.
Lemma lem3237348 {_84841 : Type'} (s : _84841 -> Prop) : (term45 _84841 s) = (term45 _84841 s).
Proof. exact (fun_ext (fun t : _84841 -> Prop => @lem3237347 _84841 s t)). Qed.
Lemma lem3237349 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237350 {_84841 : Type'} (s : _84841 -> Prop) : (term46 _84841 s) = (term46 _84841 s).
Proof. exact (MK_COMB (@lem3237349 _84841) (@lem3237348 _84841 s)). Qed.
Lemma lem3237351 {_84841 : Type'} : (term47 _84841) = (term47 _84841).
Proof. exact (fun_ext (fun s : _84841 -> Prop => @lem3237350 _84841 s)). Qed.
Lemma lem3237352 {_84841 : Type'} : (@all (_84841 -> Prop)) = (@all (_84841 -> Prop)).
Proof. exact (eq_refl (@all (_84841 -> Prop))). Qed.
Lemma lem3237353 {_84841 : Type'} : (term48 _84841) = (term48 _84841).
Proof. exact (MK_COMB (@lem3237352 _84841) (@lem3237351 _84841)). Qed.
Lemma lem3237402 {_84841 : Type'} : (term50 _84841) = (term48 _84841).
Proof. exact (TRANS (@lem3237310 _84841) (@lem3237353 _84841)). Qed.
Lemma lem3237403 {_84841 : Type'} : (term48 _84841) = (term50 _84841).
Proof. exact (SYM (@lem3237402 _84841)). Qed.
Lemma lem3237405 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3237406 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term32 _84841 s t u) = (term42 _84841 s t u)) = (term57 _84841 s t u).
Proof. exact (@lem3237405 ((term32 _84841 s t u) = (term42 _84841 s t u))). Qed.
Lemma lem3237407 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term57 _84841 s t u) = ((term32 _84841 s t u) = (term42 _84841 s t u)).
Proof. exact (SYM (@lem3237406 _84841 s t u)). Qed.
Lemma lem3237408 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term58 _84841 s t u) : term58 _84841 s t u.
Proof. exact (h1). Qed.
Lemma lem3237417 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (x : _84841) : (term59 _84841 s t x) = (term60 _84841 s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3237422 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem3237427 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term61 _84841 s t u x) = (term62 _84841 s t u x).
Proof. exact (@lem17362 (term25 _84841 s t x) (u x)). Qed.
Lemma lem3237428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237429 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (x : _84841) : (term63 _84841 s t x) = (term64 _84841 s t x).
Proof. exact (MK_COMB (@lem3237428) (@lem3237417 _84841 s t x)). Qed.
Lemma lem3237430 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term65 _84841 s t u x) = (term66 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237429 _84841 s t x) (@lem3237422 _84841 u x)). Qed.
Lemma lem3237431 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term29 _84841 s t u x) = (term65 _84841 s t u x).
Proof. exact (@lem17265 (term25 _84841 s t x) (u x)). Qed.
Lemma lem3237432 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term29 _84841 s t u x) = (term66 _84841 s t u x).
Proof. exact (TRANS (@lem3237431 _84841 s t u x) (@lem3237430 _84841 s t u x)). Qed.
Lemma lem3237433 {_84841 : Type'} (P : _84841 -> Prop) : (term67 _84841 P) = (term68 _84841 P).
Proof. exact (@lem18392 _84841 P). Qed.
Lemma lem3237434 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term69 _84841 s t u) = (term70 _84841 s t u).
Proof. exact (@lem3237433 _84841 (term31 _84841 s t u)). Qed.
Lemma lem3237435 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term71 _84841 s t u x) = (term29 _84841 s t u x).
Proof. exact (eq_refl (term71 _84841 s t u x)). Qed.
Lemma lem3237436 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3237437 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term72 _84841 s t u x) = (term61 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237436) (@lem3237435 _84841 s t u x)). Qed.
Lemma lem3237438 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term72 _84841 s t u x) = (term62 _84841 s t u x).
Proof. exact (TRANS (@lem3237437 _84841 s t u x) (@lem3237427 _84841 s t u x)). Qed.
Lemma lem3237439 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term73 _84841 s t u) = (term74 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237438 _84841 s t u x)). Qed.
Lemma lem3237440 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237441 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term70 _84841 s t u) = (term75 _84841 s t u).
Proof. exact (MK_COMB (@lem3237440 _84841) (@lem3237439 _84841 s t u)). Qed.
Lemma lem3237442 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term69 _84841 s t u) = (term75 _84841 s t u).
Proof. exact (TRANS (@lem3237434 _84841 s t u) (@lem3237441 _84841 s t u)). Qed.
Lemma lem3237443 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term31 _84841 s t u) = (term76 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237432 _84841 s t u x)). Qed.
Lemma lem3237444 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237445 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term32 _84841 s t u) = (term77 _84841 s t u).
Proof. exact (MK_COMB (@lem3237444 _84841) (@lem3237443 _84841 s t u)). Qed.
Lemma lem3237454 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term78 _84841 s u x) = (term79 _84841 s u x).
Proof. exact (@lem17362 (s x) (u x)). Qed.
Lemma lem3237459 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term37 _84841 s u x) = (term80 _84841 s u x).
Proof. exact (@lem17265 (s x) (u x)). Qed.
Lemma lem3237460 {_84841 : Type'} (P : _84841 -> Prop) : (term67 _84841 P) = (term68 _84841 P).
Proof. exact (@lem18392 _84841 P). Qed.
Lemma lem3237461 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term81 _84841 s u) = (term82 _84841 s u).
Proof. exact (@lem3237460 _84841 (term39 _84841 s u)). Qed.
Lemma lem3237462 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term83 _84841 s u x) = (term37 _84841 s u x).
Proof. exact (eq_refl (term83 _84841 s u x)). Qed.
Lemma lem3237463 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3237464 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term84 _84841 s u x) = (term78 _84841 s u x).
Proof. exact (MK_COMB (@lem3237463) (@lem3237462 _84841 s u x)). Qed.
Lemma lem3237465 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term84 _84841 s u x) = (term79 _84841 s u x).
Proof. exact (TRANS (@lem3237464 _84841 s u x) (@lem3237454 _84841 s u x)). Qed.
Lemma lem3237466 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term85 _84841 s u) = (term86 _84841 s u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237465 _84841 s u x)). Qed.
Lemma lem3237467 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237468 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term82 _84841 s u) = (term87 _84841 s u).
Proof. exact (MK_COMB (@lem3237467 _84841) (@lem3237466 _84841 s u)). Qed.
Lemma lem3237469 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term81 _84841 s u) = (term87 _84841 s u).
Proof. exact (TRANS (@lem3237461 _84841 s u) (@lem3237468 _84841 s u)). Qed.
Lemma lem3237470 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term39 _84841 s u) = (term88 _84841 s u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237459 _84841 s u x)). Qed.
Lemma lem3237471 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237472 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term40 _84841 s u) = (term89 _84841 s u).
Proof. exact (MK_COMB (@lem3237471 _84841) (@lem3237470 _84841 s u)). Qed.
Lemma lem3237481 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term78 _84841 t u x) = (term79 _84841 t u x).
Proof. exact (@lem17362 (t x) (u x)). Qed.
Lemma lem3237486 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term37 _84841 t u x) = (term80 _84841 t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3237487 {_84841 : Type'} (P : _84841 -> Prop) : (term67 _84841 P) = (term68 _84841 P).
Proof. exact (@lem18392 _84841 P). Qed.
Lemma lem3237488 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term81 _84841 t u) = (term82 _84841 t u).
Proof. exact (@lem3237487 _84841 (term39 _84841 t u)). Qed.
Lemma lem3237489 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term83 _84841 t u x) = (term37 _84841 t u x).
Proof. exact (eq_refl (term83 _84841 t u x)). Qed.
Lemma lem3237490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3237491 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term84 _84841 t u x) = (term78 _84841 t u x).
Proof. exact (MK_COMB (@lem3237490) (@lem3237489 _84841 t u x)). Qed.
Lemma lem3237492 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term84 _84841 t u x) = (term79 _84841 t u x).
Proof. exact (TRANS (@lem3237491 _84841 t u x) (@lem3237481 _84841 t u x)). Qed.
Lemma lem3237493 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term85 _84841 t u) = (term86 _84841 t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237492 _84841 t u x)). Qed.
Lemma lem3237494 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237495 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term82 _84841 t u) = (term87 _84841 t u).
Proof. exact (MK_COMB (@lem3237494 _84841) (@lem3237493 _84841 t u)). Qed.
Lemma lem3237496 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term81 _84841 t u) = (term87 _84841 t u).
Proof. exact (TRANS (@lem3237488 _84841 t u) (@lem3237495 _84841 t u)). Qed.
Lemma lem3237497 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term39 _84841 t u) = (term88 _84841 t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237486 _84841 t u x)). Qed.
Lemma lem3237498 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237499 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term40 _84841 t u) = (term89 _84841 t u).
Proof. exact (MK_COMB (@lem3237498 _84841) (@lem3237497 _84841 t u)). Qed.
Lemma lem3237500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237501 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term90 _84841 s u) = (term91 _84841 s u).
Proof. exact (MK_COMB (@lem3237500) (@lem3237469 _84841 s u)). Qed.
Lemma lem3237502 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term92 _84841 s t u) = (term93 _84841 s t u).
Proof. exact (MK_COMB (@lem3237501 _84841 s u) (@lem3237496 _84841 t u)). Qed.
Lemma lem3237503 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term94 _84841 s t u) = (term92 _84841 s t u).
Proof. exact (@lem17045 (term40 _84841 s u) (term40 _84841 t u)). Qed.
Lemma lem3237504 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term94 _84841 s t u) = (term93 _84841 s t u).
Proof. exact (TRANS (@lem3237503 _84841 s t u) (@lem3237502 _84841 s t u)). Qed.
Lemma lem3237505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237506 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term41 _84841 s u) = (term95 _84841 s u).
Proof. exact (MK_COMB (@lem3237505) (@lem3237472 _84841 s u)). Qed.
Lemma lem3237507 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term42 _84841 s t u) = (term96 _84841 s t u).
Proof. exact (MK_COMB (@lem3237506 _84841 s u) (@lem3237499 _84841 t u)). Qed.
Lemma lem3237508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237509 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term97 _84841 s t u) = (term98 _84841 s t u).
Proof. exact (MK_COMB (@lem3237508) (@lem3237442 _84841 s t u)). Qed.
Lemma lem3237510 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term99 _84841 s t u) = (term100 _84841 s t u).
Proof. exact (MK_COMB (@lem3237509 _84841 s t u) (@lem3237507 _84841 s t u)). Qed.
Lemma lem3237511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237512 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term101 _84841 s t u) = (term102 _84841 s t u).
Proof. exact (MK_COMB (@lem3237511) (@lem3237445 _84841 s t u)). Qed.
Lemma lem3237513 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term103 _84841 s t u) = (term104 _84841 s t u).
Proof. exact (MK_COMB (@lem3237512 _84841 s t u) (@lem3237504 _84841 s t u)). Qed.
Lemma lem3237514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237515 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term105 _84841 s t u) = (term106 _84841 s t u).
Proof. exact (MK_COMB (@lem3237514) (@lem3237513 _84841 s t u)). Qed.
Lemma lem3237516 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term107 _84841 s t u) = (term108 _84841 s t u).
Proof. exact (MK_COMB (@lem3237515 _84841 s t u) (@lem3237510 _84841 s t u)). Qed.
Lemma lem3237517 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term58 _84841 s t u) = (term107 _84841 s t u).
Proof. exact (@lem17646 (term32 _84841 s t u) (term42 _84841 s t u)). Qed.
Lemma lem3237518 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term58 _84841 s t u) = (term108 _84841 s t u).
Proof. exact (TRANS (@lem3237517 _84841 s t u) (@lem3237516 _84841 s t u)). Qed.
Lemma lem3237721 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3237722 {_84841 : Type'} (P : _84841 -> Prop) (Q : _84841 -> Prop) : (term109 _84841 P Q) = (term110 _84841 P Q).
Proof. exact (@lem3237721 _84841 P Q). Qed.
Lemma lem3237723 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term111 _84841 s t u) = (term112 _84841 s t u).
Proof. exact (@lem3237722 _84841 (term86 _84841 s u) (term86 _84841 t u)). Qed.
Lemma lem3237724 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term113 _84841 s u x) = (term79 _84841 s u x).
Proof. exact (eq_refl (term113 _84841 s u x)). Qed.
Lemma lem3237725 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term114 _84841 s u) = (term86 _84841 s u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237724 _84841 s u x)). Qed.
Lemma lem3237726 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237727 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term115 _84841 s u) = (term87 _84841 s u).
Proof. exact (MK_COMB (@lem3237726 _84841) (@lem3237725 _84841 s u)). Qed.
Lemma lem3237728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237729 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term116 _84841 s u) = (term91 _84841 s u).
Proof. exact (MK_COMB (@lem3237728) (@lem3237727 _84841 s u)). Qed.
Lemma lem3237730 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term113 _84841 t u x) = (term79 _84841 t u x).
Proof. exact (eq_refl (term113 _84841 t u x)). Qed.
Lemma lem3237731 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term114 _84841 t u) = (term86 _84841 t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237730 _84841 t u x)). Qed.
Lemma lem3237732 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237733 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term115 _84841 t u) = (term87 _84841 t u).
Proof. exact (MK_COMB (@lem3237732 _84841) (@lem3237731 _84841 t u)). Qed.
Lemma lem3237734 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term111 _84841 s t u) = (term93 _84841 s t u).
Proof. exact (MK_COMB (@lem3237729 _84841 s u) (@lem3237733 _84841 t u)). Qed.
Lemma lem3237735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3237736 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term117 _84841 s t u) = (term118 _84841 s t u).
Proof. exact (MK_COMB (@lem3237735) (@lem3237734 _84841 s t u)). Qed.
Lemma lem3237737 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term113 _84841 s u x) = (term79 _84841 s u x).
Proof. exact (eq_refl (term113 _84841 s u x)). Qed.
Lemma lem3237738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237739 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term119 _84841 s u x) = (term120 _84841 s u x).
Proof. exact (MK_COMB (@lem3237738) (@lem3237737 _84841 s u x)). Qed.
Lemma lem3237740 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term113 _84841 t u x) = (term79 _84841 t u x).
Proof. exact (eq_refl (term113 _84841 t u x)). Qed.
Lemma lem3237741 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term121 _84841 s t u x) = (term122 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237739 _84841 s u x) (@lem3237740 _84841 t u x)). Qed.
Lemma lem3237742 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term123 _84841 s t u) = (term124 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237741 _84841 s t u x)). Qed.
Lemma lem3237743 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237744 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term112 _84841 s t u) = (term125 _84841 s t u).
Proof. exact (MK_COMB (@lem3237743 _84841) (@lem3237742 _84841 s t u)). Qed.
Lemma lem3237745 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term111 _84841 s t u) = (term112 _84841 s t u)) = ((term93 _84841 s t u) = (term125 _84841 s t u)).
Proof. exact (MK_COMB (@lem3237736 _84841 s t u) (@lem3237744 _84841 s t u)). Qed.
Lemma lem3237746 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term93 _84841 s t u) = (term125 _84841 s t u).
Proof. exact (EQ_MP (@lem3237745 _84841 s t u) (@lem3237723 _84841 s t u)). Qed.
Lemma lem3237747 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term102 _84841 s t u) = (term102 _84841 s t u).
Proof. exact (eq_refl (term102 _84841 s t u)). Qed.
Lemma lem3237748 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term104 _84841 s t u) = (term126 _84841 s t u).
Proof. exact (MK_COMB (@lem3237747 _84841 s t u) (@lem3237746 _84841 s t u)). Qed.
Lemma lem3237750 {A : Type'} (P : Prop) (Q : A -> Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3237751 {_84841 : Type'} (P : Prop) (Q : _84841 -> Prop) : (term127 _84841 P Q) = (term128 _84841 P Q).
Proof. exact (@lem3237750 _84841 P Q). Qed.
Lemma lem3237752 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term129 _84841 s t u) = (term130 _84841 s t u).
Proof. exact (@lem3237751 _84841 (term77 _84841 s t u) (term124 _84841 s t u)). Qed.
Lemma lem3237753 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term131 _84841 s t u x) = (term122 _84841 s t u x).
Proof. exact (eq_refl (term131 _84841 s t u x)). Qed.
Lemma lem3237754 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term132 _84841 s t u) = (term124 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237753 _84841 s t u x)). Qed.
Lemma lem3237755 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237756 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term133 _84841 s t u) = (term125 _84841 s t u).
Proof. exact (MK_COMB (@lem3237755 _84841) (@lem3237754 _84841 s t u)). Qed.
Lemma lem3237757 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term102 _84841 s t u) = (term102 _84841 s t u).
Proof. exact (eq_refl (term102 _84841 s t u)). Qed.
Lemma lem3237758 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term129 _84841 s t u) = (term126 _84841 s t u).
Proof. exact (MK_COMB (@lem3237757 _84841 s t u) (@lem3237756 _84841 s t u)). Qed.
Lemma lem3237759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3237760 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term134 _84841 s t u) = (term135 _84841 s t u).
Proof. exact (MK_COMB (@lem3237759) (@lem3237758 _84841 s t u)). Qed.
Lemma lem3237761 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term131 _84841 s t u x) = (term122 _84841 s t u x).
Proof. exact (eq_refl (term131 _84841 s t u x)). Qed.
Lemma lem3237762 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term102 _84841 s t u) = (term102 _84841 s t u).
Proof. exact (eq_refl (term102 _84841 s t u)). Qed.
Lemma lem3237763 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term136 _84841 s t u x) = (term137 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237762 _84841 s t u) (@lem3237761 _84841 s t u x)). Qed.
Lemma lem3237764 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term138 _84841 s t u) = (term139 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237763 _84841 s t u x)). Qed.
Lemma lem3237765 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237766 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term130 _84841 s t u) = (term140 _84841 s t u).
Proof. exact (MK_COMB (@lem3237765 _84841) (@lem3237764 _84841 s t u)). Qed.
Lemma lem3237767 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term129 _84841 s t u) = (term130 _84841 s t u)) = ((term126 _84841 s t u) = (term140 _84841 s t u)).
Proof. exact (MK_COMB (@lem3237760 _84841 s t u) (@lem3237766 _84841 s t u)). Qed.
Lemma lem3237768 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term126 _84841 s t u) = (term140 _84841 s t u).
Proof. exact (EQ_MP (@lem3237767 _84841 s t u) (@lem3237752 _84841 s t u)). Qed.
Lemma lem3237769 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term104 _84841 s t u) = (term140 _84841 s t u).
Proof. exact (TRANS (@lem3237748 _84841 s t u) (@lem3237768 _84841 s t u)). Qed.
Lemma lem3237770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237771 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term106 _84841 s t u) = (term141 _84841 s t u).
Proof. exact (MK_COMB (@lem3237770) (@lem3237769 _84841 s t u)). Qed.
Lemma lem3237773 {A : Type'} (P : A -> Prop) (Q : Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3237774 {_84841 : Type'} (P : _84841 -> Prop) (Q : Prop) : (term142 _84841 P Q) = (term143 _84841 P Q).
Proof. exact (@lem3237773 _84841 P Q). Qed.
Lemma lem3237775 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term144 _84841 s t u) = (term145 _84841 s t u).
Proof. exact (@lem3237774 _84841 (term74 _84841 s t u) (term96 _84841 s t u)). Qed.
Lemma lem3237776 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term146 _84841 s t u x) = (term62 _84841 s t u x).
Proof. exact (eq_refl (term146 _84841 s t u x)). Qed.
Lemma lem3237777 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term147 _84841 s t u) = (term74 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237776 _84841 s t u x)). Qed.
Lemma lem3237778 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237779 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term148 _84841 s t u) = (term75 _84841 s t u).
Proof. exact (MK_COMB (@lem3237778 _84841) (@lem3237777 _84841 s t u)). Qed.
Lemma lem3237780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237781 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term149 _84841 s t u) = (term98 _84841 s t u).
Proof. exact (MK_COMB (@lem3237780) (@lem3237779 _84841 s t u)). Qed.
Lemma lem3237782 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term96 _84841 s t u) = (term96 _84841 s t u).
Proof. exact (eq_refl (term96 _84841 s t u)). Qed.
Lemma lem3237783 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term144 _84841 s t u) = (term100 _84841 s t u).
Proof. exact (MK_COMB (@lem3237781 _84841 s t u) (@lem3237782 _84841 s t u)). Qed.
Lemma lem3237784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3237785 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term150 _84841 s t u) = (term151 _84841 s t u).
Proof. exact (MK_COMB (@lem3237784) (@lem3237783 _84841 s t u)). Qed.
Lemma lem3237786 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term146 _84841 s t u x) = (term62 _84841 s t u x).
Proof. exact (eq_refl (term146 _84841 s t u x)). Qed.
Lemma lem3237787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237788 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term152 _84841 s t u x) = (term153 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237787) (@lem3237786 _84841 s t u x)). Qed.
Lemma lem3237789 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term96 _84841 s t u) = (term96 _84841 s t u).
Proof. exact (eq_refl (term96 _84841 s t u)). Qed.
Lemma lem3237790 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term154 _84841 x s t u) = (term155 _84841 x s t u).
Proof. exact (MK_COMB (@lem3237788 _84841 s t u x) (@lem3237789 _84841 s t u)). Qed.
Lemma lem3237791 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term156 _84841 s t u) = (term157 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237790 _84841 x s t u)). Qed.
Lemma lem3237792 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237793 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term145 _84841 s t u) = (term158 _84841 s t u).
Proof. exact (MK_COMB (@lem3237792 _84841) (@lem3237791 _84841 s t u)). Qed.
Lemma lem3237794 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term144 _84841 s t u) = (term145 _84841 s t u)) = ((term100 _84841 s t u) = (term158 _84841 s t u)).
Proof. exact (MK_COMB (@lem3237785 _84841 s t u) (@lem3237793 _84841 s t u)). Qed.
Lemma lem3237795 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term100 _84841 s t u) = (term158 _84841 s t u).
Proof. exact (EQ_MP (@lem3237794 _84841 s t u) (@lem3237775 _84841 s t u)). Qed.
Lemma lem3237796 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term108 _84841 s t u) = (term159 _84841 s t u).
Proof. exact (MK_COMB (@lem3237771 _84841 s t u) (@lem3237795 _84841 s t u)). Qed.
Lemma lem3237798 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3237799 {_84841 : Type'} (P : _84841 -> Prop) (Q : _84841 -> Prop) : (term109 _84841 P Q) = (term110 _84841 P Q).
Proof. exact (@lem3237798 _84841 P Q). Qed.
Lemma lem3237800 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term160 _84841 s t u) = (term161 _84841 s t u).
Proof. exact (@lem3237799 _84841 (term139 _84841 s t u) (term157 _84841 s t u)). Qed.
Lemma lem3237801 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term162 _84841 s t u x) = (term137 _84841 s t u x).
Proof. exact (eq_refl (term162 _84841 s t u x)). Qed.
Lemma lem3237802 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term163 _84841 s t u) = (term139 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237801 _84841 s t u x)). Qed.
Lemma lem3237803 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237804 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term164 _84841 s t u) = (term140 _84841 s t u).
Proof. exact (MK_COMB (@lem3237803 _84841) (@lem3237802 _84841 s t u)). Qed.
Lemma lem3237805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237806 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term165 _84841 s t u) = (term141 _84841 s t u).
Proof. exact (MK_COMB (@lem3237805) (@lem3237804 _84841 s t u)). Qed.
Lemma lem3237807 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term166 _84841 s t u x) = (term155 _84841 x s t u).
Proof. exact (eq_refl (term166 _84841 s t u x)). Qed.
Lemma lem3237808 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term167 _84841 s t u) = (term157 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237807 _84841 x s t u)). Qed.
Lemma lem3237809 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237810 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term168 _84841 s t u) = (term158 _84841 s t u).
Proof. exact (MK_COMB (@lem3237809 _84841) (@lem3237808 _84841 s t u)). Qed.
Lemma lem3237811 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term160 _84841 s t u) = (term159 _84841 s t u).
Proof. exact (MK_COMB (@lem3237806 _84841 s t u) (@lem3237810 _84841 s t u)). Qed.
Lemma lem3237812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3237813 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term169 _84841 s t u) = (term170 _84841 s t u).
Proof. exact (MK_COMB (@lem3237812) (@lem3237811 _84841 s t u)). Qed.
Lemma lem3237814 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term162 _84841 s t u x) = (term137 _84841 s t u x).
Proof. exact (eq_refl (term162 _84841 s t u x)). Qed.
Lemma lem3237815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237816 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term171 _84841 s t u x) = (term172 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237815) (@lem3237814 _84841 s t u x)). Qed.
Lemma lem3237817 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term166 _84841 s t u x) = (term155 _84841 x s t u).
Proof. exact (eq_refl (term166 _84841 s t u x)). Qed.
Lemma lem3237818 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term173 _84841 s t u x) = (term174 _84841 x s t u).
Proof. exact (MK_COMB (@lem3237816 _84841 s t u x) (@lem3237817 _84841 x s t u)). Qed.
Lemma lem3237819 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term175 _84841 s t u) = (term176 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237818 _84841 x s t u)). Qed.
Lemma lem3237820 {_84841 : Type'} : (@ex _84841) = (@ex _84841).
Proof. exact (eq_refl (@ex _84841)). Qed.
Lemma lem3237821 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term161 _84841 s t u) = (term177 _84841 s t u).
Proof. exact (MK_COMB (@lem3237820 _84841) (@lem3237819 _84841 s t u)). Qed.
Lemma lem3237822 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : ((term160 _84841 s t u) = (term161 _84841 s t u)) = ((term159 _84841 s t u) = (term177 _84841 s t u)).
Proof. exact (MK_COMB (@lem3237813 _84841 s t u) (@lem3237821 _84841 s t u)). Qed.
Lemma lem3237823 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term159 _84841 s t u) = (term177 _84841 s t u).
Proof. exact (EQ_MP (@lem3237822 _84841 s t u) (@lem3237800 _84841 s t u)). Qed.
Lemma lem3237825 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term108 _84841 s t u) = (term177 _84841 s t u).
Proof. exact (TRANS (@lem3237796 _84841 s t u) (@lem3237823 _84841 s t u)). Qed.
Lemma lem3237826 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term58 _84841 s t u) = (term177 _84841 s t u).
Proof. exact (TRANS (@lem3237518 _84841 s t u) (@lem3237825 _84841 s t u)). Qed.
Lemma lem3237827 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term58 _84841 s t u) : term177 _84841 s t u.
Proof. exact (EQ_MP (@lem3237826 _84841 s t u) (@lem3237408 _84841 s t u h1)). Qed.
Lemma lem3237828 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term174 _84841 x s t u) : term174 _84841 x s t u.
Proof. exact (h1). Qed.
Lemma lem3237839 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term80 _84841 t u x) = (term80 _84841 t u x).
Proof. exact (eq_refl (term80 _84841 t u x)). Qed.
Lemma lem3237840 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term88 _84841 t u) = (term88 _84841 t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237839 _84841 t u x)). Qed.
Lemma lem3237841 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237842 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term89 _84841 t u) = (term89 _84841 t u).
Proof. exact (MK_COMB (@lem3237841 _84841) (@lem3237840 _84841 t u)). Qed.
Lemma lem3237853 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term80 _84841 s u x) = (term80 _84841 s u x).
Proof. exact (eq_refl (term80 _84841 s u x)). Qed.
Lemma lem3237854 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term88 _84841 s u) = (term88 _84841 s u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237853 _84841 s u x)). Qed.
Lemma lem3237855 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237856 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term89 _84841 s u) = (term89 _84841 s u).
Proof. exact (MK_COMB (@lem3237855 _84841) (@lem3237854 _84841 s u)). Qed.
Lemma lem3237857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237858 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term95 _84841 s u) = (term95 _84841 s u).
Proof. exact (MK_COMB (@lem3237857) (@lem3237856 _84841 s u)). Qed.
Lemma lem3237859 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term96 _84841 s t u) = (term96 _84841 s t u).
Proof. exact (MK_COMB (@lem3237858 _84841 s u) (@lem3237842 _84841 t u)). Qed.
Lemma lem3237878 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term153 _84841 s t u x) = (term153 _84841 s t u x).
Proof. exact (eq_refl (term153 _84841 s t u x)). Qed.
Lemma lem3237879 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term155 _84841 x s t u) = (term155 _84841 x s t u).
Proof. exact (MK_COMB (@lem3237878 _84841 s t u x) (@lem3237859 _84841 s t u)). Qed.
Lemma lem3237904 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term122 _84841 s t u x) = (term122 _84841 s t u x).
Proof. exact (eq_refl (term122 _84841 s t u x)). Qed.
Lemma lem3237923 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term66 _84841 s t u x) = (term66 _84841 s t u x).
Proof. exact (eq_refl (term66 _84841 s t u x)). Qed.
Lemma lem3237924 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term76 _84841 s t u) = (term76 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237923 _84841 s t u x)). Qed.
Lemma lem3237925 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237926 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term77 _84841 s t u) = (term77 _84841 s t u).
Proof. exact (MK_COMB (@lem3237925 _84841) (@lem3237924 _84841 s t u)). Qed.
Lemma lem3237927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3237928 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term102 _84841 s t u) = (term102 _84841 s t u).
Proof. exact (MK_COMB (@lem3237927) (@lem3237926 _84841 s t u)). Qed.
Lemma lem3237929 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term137 _84841 s t u x) = (term137 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237928 _84841 s t u) (@lem3237904 _84841 s t u x)). Qed.
Lemma lem3237930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3237931 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term172 _84841 s t u x) = (term172 _84841 s t u x).
Proof. exact (MK_COMB (@lem3237930) (@lem3237929 _84841 s t u x)). Qed.
Lemma lem3237932 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term174 _84841 x s t u) = (term174 _84841 x s t u).
Proof. exact (MK_COMB (@lem3237931 _84841 s t u x) (@lem3237879 _84841 x s t u)). Qed.
Lemma lem3237933 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term174 _84841 x s t u) : term174 _84841 x s t u.
Proof. exact (EQ_MP (@lem3237932 _84841 x s t u) (@lem3237828 _84841 x s t u h1)). Qed.
Lemma lem3237934 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term137 _84841 s t u x.
Proof. exact (h1). Qed.
Lemma lem3237935 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term155 _84841 x s t u.
Proof. exact (h1). Qed.
Lemma lem3237936 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term122 _84841 s t u x.
Proof. exact (proj2 (@lem3237934 _84841 s t u x h1)). Qed.
Lemma lem3237937 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term77 _84841 s t u.
Proof. exact (proj1 (@lem3237934 _84841 s t u x h1)). Qed.
Lemma lem3237938 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 s u x) : term79 _84841 s u x.
Proof. exact (h1). Qed.
Lemma lem3237939 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 t u x) : term79 _84841 t u x.
Proof. exact (h1). Qed.
Lemma lem3237944 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term96 _84841 s t u.
Proof. exact (proj2 (@lem3237935 _84841 x s t u h1)). Qed.
Lemma lem3237945 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term62 _84841 s t u x.
Proof. exact (proj1 (@lem3237935 _84841 x s t u h1)). Qed.
Lemma lem3237946 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term89 _84841 t u.
Proof. exact (proj2 (@lem3237944 _84841 x s t u h1)). Qed.
Lemma lem3237947 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term89 _84841 s u.
Proof. exact (proj1 (@lem3237944 _84841 x s t u h1)). Qed.
Lemma lem3237949 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term25 _84841 s t x.
Proof. exact (proj1 (@lem3237945 _84841 x s t u h1)). Qed.
Lemma lem3237969 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term66 _84841 s t u x) = (term178 _84841 s t u x).
Proof. exact (@lem19699 (term179 _84841 s x) (term179 _84841 t x) (u x)). Qed.
Lemma lem3237970 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term76 _84841 s t u) = (term180 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3237969 _84841 s t u x)). Qed.
Lemma lem3237971 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3237973 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term77 _84841 s t u) = (term181 _84841 s t u).
Proof. exact (MK_COMB (@lem3237971 _84841) (@lem3237970 _84841 s t u)). Qed.
Lemma lem3237974 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term181 _84841 s t u.
Proof. exact (EQ_MP (@lem3237973 _84841 s t u) (@lem3237937 _84841 s t u x h1)). Qed.
Lemma lem3238000 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term66 _84841 s t u x) = (term178 _84841 s t u x).
Proof. exact (@lem19699 (term179 _84841 s x) (term179 _84841 t x) (u x)). Qed.
Lemma lem3238001 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term76 _84841 s t u) = (term180 _84841 s t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3238000 _84841 s t u x)). Qed.
Lemma lem3238002 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3238004 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term77 _84841 s t u) = (term181 _84841 s t u).
Proof. exact (MK_COMB (@lem3238002 _84841) (@lem3238001 _84841 s t u)). Qed.
Lemma lem3238005 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term181 _84841 s t u.
Proof. exact (EQ_MP (@lem3238004 _84841 s t u) (@lem3237937 _84841 s t u x h1)). Qed.
Lemma lem3238021 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term80 _84841 s u x) = (term80 _84841 s u x).
Proof. exact (eq_refl (term80 _84841 s u x)). Qed.
Lemma lem3238022 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term88 _84841 s u) = (term88 _84841 s u).
Proof. exact (fun_ext (fun x : _84841 => @lem3238021 _84841 s u x)). Qed.
Lemma lem3238023 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3238025 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) : (term89 _84841 s u) = (term89 _84841 s u).
Proof. exact (MK_COMB (@lem3238023 _84841) (@lem3238022 _84841 s u)). Qed.
Lemma lem3238026 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term89 _84841 s u.
Proof. exact (EQ_MP (@lem3238025 _84841 s u) (@lem3237947 _84841 x s t u h1)). Qed.
Lemma lem3238047 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3238068 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) : (term80 _84841 t u x) = (term80 _84841 t u x).
Proof. exact (eq_refl (term80 _84841 t u x)). Qed.
Lemma lem3238069 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term88 _84841 t u) = (term88 _84841 t u).
Proof. exact (fun_ext (fun x : _84841 => @lem3238068 _84841 t u x)). Qed.
Lemma lem3238070 {_84841 : Type'} : (@all _84841) = (@all _84841).
Proof. exact (eq_refl (@all _84841)). Qed.
Lemma lem3238072 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) : (term89 _84841 t u) = (term89 _84841 t u).
Proof. exact (MK_COMB (@lem3238070 _84841) (@lem3238069 _84841 t u)). Qed.
Lemma lem3238073 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term89 _84841 t u.
Proof. exact (EQ_MP (@lem3238072 _84841 t u) (@lem3237946 _84841 x s t u h1)). Qed.
Lemma lem3238081 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3238082 {_84841 : Type'} (_33213 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term182 _84841 s t u _33213.
Proof. exact (@lem3237974 _84841 s t u x h1 _33213). Qed.
Lemma lem3238083 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (_33213 : _84841) : (term182 _84841 s t u _33213) = (term178 _84841 s t u _33213).
Proof. exact (eq_refl (term182 _84841 s t u _33213)). Qed.
Lemma lem3238084 {_84841 : Type'} (_33213 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term178 _84841 s t u _33213.
Proof. exact (EQ_MP (@lem3238083 _84841 s t u _33213) (@lem3238082 _84841 _33213 s t u x h1)). Qed.
Lemma lem3238085 {_84841 : Type'} (_33214 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term182 _84841 s t u _33214.
Proof. exact (@lem3238005 _84841 s t u x h1 _33214). Qed.
Lemma lem3238086 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (_33214 : _84841) : (term182 _84841 s t u _33214) = (term178 _84841 s t u _33214).
Proof. exact (eq_refl (term182 _84841 s t u _33214)). Qed.
Lemma lem3238087 {_84841 : Type'} (_33214 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term178 _84841 s t u _33214.
Proof. exact (EQ_MP (@lem3238086 _84841 s t u _33214) (@lem3238085 _84841 _33214 s t u x h1)). Qed.
Lemma lem3238088 {_84841 : Type'} (_33215 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term183 _84841 s u _33215.
Proof. exact (@lem3238026 _84841 x s t u h1 _33215). Qed.
Lemma lem3238089 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (_33215 : _84841) : (term183 _84841 s u _33215) = (term80 _84841 s u _33215).
Proof. exact (eq_refl (term183 _84841 s u _33215)). Qed.
Lemma lem3238097 {_84841 : Type'} (_33218 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term183 _84841 t u _33218.
Proof. exact (@lem3238073 _84841 x s t u h1 _33218). Qed.
Lemma lem3238098 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (_33218 : _84841) : (term183 _84841 t u _33218) = (term80 _84841 t u _33218).
Proof. exact (eq_refl (term183 _84841 t u _33218)). Qed.
Lemma lem3238107 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 s u x) : term179 _84841 u x.
Proof. exact (proj2 (@lem3237938 _84841 s u x h1)). Qed.
Lemma lem3238113 {_84841 : Type'} (_33213 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term80 _84841 s u _33213.
Proof. exact (proj1 (@lem3238084 _84841 _33213 s t u x h1)). Qed.
Lemma lem3238123 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 t u x) : term179 _84841 u x.
Proof. exact (proj2 (@lem3237939 _84841 t u x h1)). Qed.
Lemma lem3238135 {_84841 : Type'} (_33214 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term80 _84841 t u _33214.
Proof. exact (proj2 (@lem3238087 _84841 _33214 s t u x h1)). Qed.
Lemma lem3238141 {_84841 : Type'} (_33215 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term80 _84841 s u _33215.
Proof. exact (EQ_MP (@lem3238089 _84841 s u _33215) (@lem3238088 _84841 _33215 x s t u h1)). Qed.
Lemma lem3238149 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term179 _84841 u x.
Proof. exact (proj2 (@lem3237945 _84841 x s t u h1)). Qed.
Lemma lem3238151 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3238163 {_84841 : Type'} (_33218 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term80 _84841 t u _33218.
Proof. exact (EQ_MP (@lem3238098 _84841 t u _33218) (@lem3238097 _84841 _33218 x s t u h1)). Qed.
Lemma lem3238165 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term179 _84841 u x.
Proof. exact (proj2 (@lem3237945 _84841 x s t u h1)). Qed.
Lemma lem3238167 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3238169 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 s u x) : s x.
Proof. exact (proj1 (@lem3237938 _84841 s u x h1)). Qed.
Lemma lem3238170 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 s u x) : term184 _84841 s x.
Proof. exact (fun h0 : term179 _84841 s x => @lem3238169 _84841 s u x h1). Qed.
Lemma lem3238172 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238173 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) : (term184 _84841 s x) = (s x).
Proof. exact (@lem3238172 (s x)). Qed.
Lemma lem3238174 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 s u x) : s x.
Proof. exact (EQ_MP (@lem3238173 _84841 s x) (@lem3238170 _84841 s u x h1)). Qed.
Lemma lem3238180 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3238181 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : (term80 _84841 s u _33213) = (term186 _84841 u s _33213).
Proof. exact (@lem3238180 (u _33213) (term179 _84841 s _33213)). Qed.
Lemma lem3238187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238188 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : (term187 _84841 s u _33213) = (term188 _84841 u s _33213).
Proof. exact (MK_COMB (@lem3238187) (@lem3238181 _84841 u s _33213)). Qed.
Lemma lem3238194 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : (term186 _84841 u s _33213) = (term186 _84841 u s _33213).
Proof. exact (eq_refl (term186 _84841 u s _33213)). Qed.
Lemma lem3238195 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : ((term80 _84841 s u _33213) = (term186 _84841 u s _33213)) = ((term186 _84841 u s _33213) = (term186 _84841 u s _33213)).
Proof. exact (MK_COMB (@lem3238188 _84841 u s _33213) (@lem3238194 _84841 u s _33213)). Qed.
Lemma lem3238197 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3238198 (x : Prop) : (x = x) = True.
Proof. exact (@lem3238197 Prop x). Qed.
Lemma lem3238199 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : ((term186 _84841 u s _33213) = (term186 _84841 u s _33213)) = True.
Proof. exact (@lem3238198 (term186 _84841 u s _33213)). Qed.
Lemma lem3238200 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : ((term80 _84841 s u _33213) = (term186 _84841 u s _33213)) = True.
Proof. exact (TRANS (@lem3238195 _84841 u s _33213) (@lem3238199 _84841 u s _33213)). Qed.
Lemma lem3238201 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : True = ((term80 _84841 s u _33213) = (term186 _84841 u s _33213)).
Proof. exact (SYM (@lem3238200 _84841 u s _33213)). Qed.
Lemma lem3238202 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33213 : _84841) : (term80 _84841 s u _33213) = (term186 _84841 u s _33213).
Proof. exact (EQ_MP (@lem3238201 _84841 u s _33213) (@lem0)). Qed.
Lemma lem3238203 {_84841 : Type'} (_33213 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term186 _84841 u s _33213.
Proof. exact (EQ_MP (@lem3238202 _84841 u s _33213) (@lem3238113 _84841 _33213 s t u x h1)). Qed.
Lemma lem3238205 (b : Prop) (a : Prop) : (a \/ b) = (term189 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3238206 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (_33213 : _84841) : (term186 _84841 u s _33213) = (term190 _84841 s u _33213).
Proof. exact (@lem3238205 (term179 _84841 s _33213) (u _33213)). Qed.
Lemma lem3238208 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3238209 {_84841 : Type'} (s : _84841 -> Prop) (_33213 : _84841) : (term191 _84841 s _33213) = (s _33213).
Proof. exact (@lem3238208 (s _33213)). Qed.
Lemma lem3238210 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3238211 {_84841 : Type'} (s : _84841 -> Prop) (_33213 : _84841) : (term192 _84841 s _33213) = (term35 _84841 s _33213).
Proof. exact (MK_COMB (@lem3238210) (@lem3238209 _84841 s _33213)). Qed.
Lemma lem3238212 {_84841 : Type'} (u : _84841 -> Prop) (_33213 : _84841) : (u _33213) = (u _33213).
Proof. exact (eq_refl (u _33213)). Qed.
Lemma lem3238213 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (_33213 : _84841) : (term190 _84841 s u _33213) = (term37 _84841 s u _33213).
Proof. exact (MK_COMB (@lem3238211 _84841 s _33213) (@lem3238212 _84841 u _33213)). Qed.
Lemma lem3238214 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (_33213 : _84841) : (term186 _84841 u s _33213) = (term37 _84841 s u _33213).
Proof. exact (TRANS (@lem3238206 _84841 s u _33213) (@lem3238213 _84841 s u _33213)). Qed.
Lemma lem3238217 {_84841 : Type'} (_33213 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term37 _84841 s u _33213.
Proof. exact (EQ_MP (@lem3238214 _84841 s u _33213) (@lem3238203 _84841 _33213 s t u x h1)). Qed.
Lemma lem3238218 {_84841 : Type'} (_33213 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term37 _84841 s u _33213.
Proof. exact (@lem3238217 _84841 _33213 s t u x h1). Qed.
Lemma lem3238219 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term37 _84841 s u x.
Proof. exact (@lem3238218 _84841 x s t u x h1). Qed.
Lemma lem3238222 {_84841 : Type'} (t : _84841 -> Prop) (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 s u x) : u x.
Proof. exact (@lem3238219 _84841 s t u x h1 (@lem3238174 _84841 s u x h2)). Qed.
Lemma lem3238223 {_84841 : Type'} (t : _84841 -> Prop) (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 s u x) : term184 _84841 u x.
Proof. exact (fun h0 : term179 _84841 u x => @lem3238222 _84841 t s u x h1 h2). Qed.
Lemma lem3238225 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238226 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term184 _84841 u x) = (u x).
Proof. exact (@lem3238225 (u x)). Qed.
Lemma lem3238227 {_84841 : Type'} (t : _84841 -> Prop) (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 s u x) : u x.
Proof. exact (EQ_MP (@lem3238226 _84841 u x) (@lem3238223 _84841 t s u x h1 h2)). Qed.
Lemma lem3238230 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3238232 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term179 _84841 u x) = (term193 _84841 u x).
Proof. exact (@lem3238230 (u x)). Qed.
Lemma lem3238235 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 s u x) : term193 _84841 u x.
Proof. exact (EQ_MP (@lem3238232 _84841 u x) (@lem3238107 _84841 s u x h1)). Qed.
Lemma lem3238238 {_84841 : Type'} (t : _84841 -> Prop) (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 s u x) : False.
Proof. exact (@lem3238235 _84841 s u x h2 (@lem3238227 _84841 t s u x h1 h2)). Qed.
Lemma lem3238239 {_84841 : Type'} (t : _84841 -> Prop) (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 s u x) : term194.
Proof. exact (fun h0 : ~ False => @lem3238238 _84841 t s u x h1 h2). Qed.
Lemma lem3238241 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238242 : term194 = False.
Proof. exact (@lem3238241 False). Qed.
Lemma lem3238243 {_84841 : Type'} (t : _84841 -> Prop) (s : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 s u x) : False.
Proof. exact (EQ_MP (@lem3238242) (@lem3238239 _84841 t s u x h1 h2)). Qed.
Lemma lem3238245 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 t u x) : t x.
Proof. exact (proj1 (@lem3237939 _84841 t u x h1)). Qed.
Lemma lem3238246 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 t u x) : term184 _84841 t x.
Proof. exact (fun h0 : term179 _84841 t x => @lem3238245 _84841 t u x h1). Qed.
Lemma lem3238248 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238249 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) : (term184 _84841 t x) = (t x).
Proof. exact (@lem3238248 (t x)). Qed.
Lemma lem3238250 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 t u x) : t x.
Proof. exact (EQ_MP (@lem3238249 _84841 t x) (@lem3238246 _84841 t u x h1)). Qed.
Lemma lem3238256 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3238257 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : (term80 _84841 t u _33214) = (term186 _84841 u t _33214).
Proof. exact (@lem3238256 (u _33214) (term179 _84841 t _33214)). Qed.
Lemma lem3238263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238264 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : (term187 _84841 t u _33214) = (term188 _84841 u t _33214).
Proof. exact (MK_COMB (@lem3238263) (@lem3238257 _84841 u t _33214)). Qed.
Lemma lem3238270 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : (term186 _84841 u t _33214) = (term186 _84841 u t _33214).
Proof. exact (eq_refl (term186 _84841 u t _33214)). Qed.
Lemma lem3238271 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : ((term80 _84841 t u _33214) = (term186 _84841 u t _33214)) = ((term186 _84841 u t _33214) = (term186 _84841 u t _33214)).
Proof. exact (MK_COMB (@lem3238264 _84841 u t _33214) (@lem3238270 _84841 u t _33214)). Qed.
Lemma lem3238273 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3238274 (x : Prop) : (x = x) = True.
Proof. exact (@lem3238273 Prop x). Qed.
Lemma lem3238275 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : ((term186 _84841 u t _33214) = (term186 _84841 u t _33214)) = True.
Proof. exact (@lem3238274 (term186 _84841 u t _33214)). Qed.
Lemma lem3238276 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : ((term80 _84841 t u _33214) = (term186 _84841 u t _33214)) = True.
Proof. exact (TRANS (@lem3238271 _84841 u t _33214) (@lem3238275 _84841 u t _33214)). Qed.
Lemma lem3238277 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : True = ((term80 _84841 t u _33214) = (term186 _84841 u t _33214)).
Proof. exact (SYM (@lem3238276 _84841 u t _33214)). Qed.
Lemma lem3238278 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33214 : _84841) : (term80 _84841 t u _33214) = (term186 _84841 u t _33214).
Proof. exact (EQ_MP (@lem3238277 _84841 u t _33214) (@lem0)). Qed.
Lemma lem3238279 {_84841 : Type'} (_33214 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term186 _84841 u t _33214.
Proof. exact (EQ_MP (@lem3238278 _84841 u t _33214) (@lem3238135 _84841 _33214 s t u x h1)). Qed.
Lemma lem3238281 (b : Prop) (a : Prop) : (a \/ b) = (term189 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3238282 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (_33214 : _84841) : (term186 _84841 u t _33214) = (term190 _84841 t u _33214).
Proof. exact (@lem3238281 (term179 _84841 t _33214) (u _33214)). Qed.
Lemma lem3238284 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3238285 {_84841 : Type'} (t : _84841 -> Prop) (_33214 : _84841) : (term191 _84841 t _33214) = (t _33214).
Proof. exact (@lem3238284 (t _33214)). Qed.
Lemma lem3238286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3238287 {_84841 : Type'} (t : _84841 -> Prop) (_33214 : _84841) : (term192 _84841 t _33214) = (term35 _84841 t _33214).
Proof. exact (MK_COMB (@lem3238286) (@lem3238285 _84841 t _33214)). Qed.
Lemma lem3238288 {_84841 : Type'} (u : _84841 -> Prop) (_33214 : _84841) : (u _33214) = (u _33214).
Proof. exact (eq_refl (u _33214)). Qed.
Lemma lem3238289 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (_33214 : _84841) : (term190 _84841 t u _33214) = (term37 _84841 t u _33214).
Proof. exact (MK_COMB (@lem3238287 _84841 t _33214) (@lem3238288 _84841 u _33214)). Qed.
Lemma lem3238290 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (_33214 : _84841) : (term186 _84841 u t _33214) = (term37 _84841 t u _33214).
Proof. exact (TRANS (@lem3238282 _84841 t u _33214) (@lem3238289 _84841 t u _33214)). Qed.
Lemma lem3238293 {_84841 : Type'} (_33214 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term37 _84841 t u _33214.
Proof. exact (EQ_MP (@lem3238290 _84841 t u _33214) (@lem3238279 _84841 _33214 s t u x h1)). Qed.
Lemma lem3238294 {_84841 : Type'} (_33214 : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term37 _84841 t u _33214.
Proof. exact (@lem3238293 _84841 _33214 s t u x h1). Qed.
Lemma lem3238295 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : term37 _84841 t u x.
Proof. exact (@lem3238294 _84841 x s t u x h1). Qed.
Lemma lem3238298 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 t u x) : u x.
Proof. exact (@lem3238295 _84841 s t u x h1 (@lem3238250 _84841 t u x h2)). Qed.
Lemma lem3238299 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 t u x) : term184 _84841 u x.
Proof. exact (fun h0 : term179 _84841 u x => @lem3238298 _84841 s t u x h1 h2). Qed.
Lemma lem3238301 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238302 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term184 _84841 u x) = (u x).
Proof. exact (@lem3238301 (u x)). Qed.
Lemma lem3238303 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 t u x) : u x.
Proof. exact (EQ_MP (@lem3238302 _84841 u x) (@lem3238299 _84841 s t u x h1 h2)). Qed.
Lemma lem3238306 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3238308 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term179 _84841 u x) = (term193 _84841 u x).
Proof. exact (@lem3238306 (u x)). Qed.
Lemma lem3238311 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term79 _84841 t u x) : term193 _84841 u x.
Proof. exact (EQ_MP (@lem3238308 _84841 u x) (@lem3238123 _84841 t u x h1)). Qed.
Lemma lem3238314 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 t u x) : False.
Proof. exact (@lem3238311 _84841 t u x h2 (@lem3238303 _84841 s t u x h1 h2)). Qed.
Lemma lem3238315 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 t u x) : term194.
Proof. exact (fun h0 : ~ False => @lem3238314 _84841 s t u x h1 h2). Qed.
Lemma lem3238317 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238318 : term194 = False.
Proof. exact (@lem3238317 False). Qed.
Lemma lem3238319 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) (h2 : term79 _84841 t u x) : False.
Proof. exact (EQ_MP (@lem3238318) (@lem3238315 _84841 s t u x h1 h2)). Qed.
Lemma lem3238321 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3238322 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) (h1 : s x) : term184 _84841 s x.
Proof. exact (fun h0 : term179 _84841 s x => @lem3238321 _84841 s x h1). Qed.
Lemma lem3238324 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238325 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) : (term184 _84841 s x) = (s x).
Proof. exact (@lem3238324 (s x)). Qed.
Lemma lem3238326 {_84841 : Type'} (s : _84841 -> Prop) (x : _84841) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3238325 _84841 s x) (@lem3238322 _84841 s x h1)). Qed.
Lemma lem3238332 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3238333 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : (term80 _84841 s u _33215) = (term186 _84841 u s _33215).
Proof. exact (@lem3238332 (u _33215) (term179 _84841 s _33215)). Qed.
Lemma lem3238339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238340 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : (term187 _84841 s u _33215) = (term188 _84841 u s _33215).
Proof. exact (MK_COMB (@lem3238339) (@lem3238333 _84841 u s _33215)). Qed.
Lemma lem3238346 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : (term186 _84841 u s _33215) = (term186 _84841 u s _33215).
Proof. exact (eq_refl (term186 _84841 u s _33215)). Qed.
Lemma lem3238347 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : ((term80 _84841 s u _33215) = (term186 _84841 u s _33215)) = ((term186 _84841 u s _33215) = (term186 _84841 u s _33215)).
Proof. exact (MK_COMB (@lem3238340 _84841 u s _33215) (@lem3238346 _84841 u s _33215)). Qed.
Lemma lem3238349 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3238350 (x : Prop) : (x = x) = True.
Proof. exact (@lem3238349 Prop x). Qed.
Lemma lem3238351 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : ((term186 _84841 u s _33215) = (term186 _84841 u s _33215)) = True.
Proof. exact (@lem3238350 (term186 _84841 u s _33215)). Qed.
Lemma lem3238352 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : ((term80 _84841 s u _33215) = (term186 _84841 u s _33215)) = True.
Proof. exact (TRANS (@lem3238347 _84841 u s _33215) (@lem3238351 _84841 u s _33215)). Qed.
Lemma lem3238353 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : True = ((term80 _84841 s u _33215) = (term186 _84841 u s _33215)).
Proof. exact (SYM (@lem3238352 _84841 u s _33215)). Qed.
Lemma lem3238354 {_84841 : Type'} (u : _84841 -> Prop) (s : _84841 -> Prop) (_33215 : _84841) : (term80 _84841 s u _33215) = (term186 _84841 u s _33215).
Proof. exact (EQ_MP (@lem3238353 _84841 u s _33215) (@lem0)). Qed.
Lemma lem3238355 {_84841 : Type'} (_33215 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term186 _84841 u s _33215.
Proof. exact (EQ_MP (@lem3238354 _84841 u s _33215) (@lem3238141 _84841 _33215 x s t u h1)). Qed.
Lemma lem3238357 (b : Prop) (a : Prop) : (a \/ b) = (term189 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3238358 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (_33215 : _84841) : (term186 _84841 u s _33215) = (term190 _84841 s u _33215).
Proof. exact (@lem3238357 (term179 _84841 s _33215) (u _33215)). Qed.
Lemma lem3238360 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3238361 {_84841 : Type'} (s : _84841 -> Prop) (_33215 : _84841) : (term191 _84841 s _33215) = (s _33215).
Proof. exact (@lem3238360 (s _33215)). Qed.
Lemma lem3238362 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3238363 {_84841 : Type'} (s : _84841 -> Prop) (_33215 : _84841) : (term192 _84841 s _33215) = (term35 _84841 s _33215).
Proof. exact (MK_COMB (@lem3238362) (@lem3238361 _84841 s _33215)). Qed.
Lemma lem3238364 {_84841 : Type'} (u : _84841 -> Prop) (_33215 : _84841) : (u _33215) = (u _33215).
Proof. exact (eq_refl (u _33215)). Qed.
Lemma lem3238365 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (_33215 : _84841) : (term190 _84841 s u _33215) = (term37 _84841 s u _33215).
Proof. exact (MK_COMB (@lem3238363 _84841 s _33215) (@lem3238364 _84841 u _33215)). Qed.
Lemma lem3238366 {_84841 : Type'} (s : _84841 -> Prop) (u : _84841 -> Prop) (_33215 : _84841) : (term186 _84841 u s _33215) = (term37 _84841 s u _33215).
Proof. exact (TRANS (@lem3238358 _84841 s u _33215) (@lem3238365 _84841 s u _33215)). Qed.
Lemma lem3238369 {_84841 : Type'} (_33215 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term37 _84841 s u _33215.
Proof. exact (EQ_MP (@lem3238366 _84841 s u _33215) (@lem3238355 _84841 _33215 x s t u h1)). Qed.
Lemma lem3238370 {_84841 : Type'} (_33215 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term37 _84841 s u _33215.
Proof. exact (@lem3238369 _84841 _33215 x s t u h1). Qed.
Lemma lem3238371 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term37 _84841 s u x.
Proof. exact (@lem3238370 _84841 x x s t u h1). Qed.
Lemma lem3238374 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : u x.
Proof. exact (@lem3238371 _84841 x s t u h2 (@lem3238326 _84841 s x h1)). Qed.
Lemma lem3238375 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : term184 _84841 u x.
Proof. exact (fun h0 : term179 _84841 u x => @lem3238374 _84841 x s t u h1 h2). Qed.
Lemma lem3238377 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238378 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term184 _84841 u x) = (u x).
Proof. exact (@lem3238377 (u x)). Qed.
Lemma lem3238379 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : u x.
Proof. exact (EQ_MP (@lem3238378 _84841 u x) (@lem3238375 _84841 x s t u h1 h2)). Qed.
Lemma lem3238382 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3238384 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term179 _84841 u x) = (term193 _84841 u x).
Proof. exact (@lem3238382 (u x)). Qed.
Lemma lem3238387 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term193 _84841 u x.
Proof. exact (EQ_MP (@lem3238384 _84841 u x) (@lem3238149 _84841 x s t u h1)). Qed.
Lemma lem3238390 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (@lem3238387 _84841 x s t u h2 (@lem3238379 _84841 x s t u h1 h2)). Qed.
Lemma lem3238391 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : term194.
Proof. exact (fun h0 : ~ False => @lem3238390 _84841 x s t u h1 h2). Qed.
Lemma lem3238393 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238394 : term194 = False.
Proof. exact (@lem3238393 False). Qed.
Lemma lem3238395 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238394) (@lem3238391 _84841 x s t u h1 h2)). Qed.
Lemma lem3238397 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3238398 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) (h1 : t x) : term184 _84841 t x.
Proof. exact (fun h0 : term179 _84841 t x => @lem3238397 _84841 t x h1). Qed.
Lemma lem3238400 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238401 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) : (term184 _84841 t x) = (t x).
Proof. exact (@lem3238400 (t x)). Qed.
Lemma lem3238402 {_84841 : Type'} (t : _84841 -> Prop) (x : _84841) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3238401 _84841 t x) (@lem3238398 _84841 t x h1)). Qed.
Lemma lem3238408 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3238409 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : (term80 _84841 t u _33218) = (term186 _84841 u t _33218).
Proof. exact (@lem3238408 (u _33218) (term179 _84841 t _33218)). Qed.
Lemma lem3238415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3238416 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : (term187 _84841 t u _33218) = (term188 _84841 u t _33218).
Proof. exact (MK_COMB (@lem3238415) (@lem3238409 _84841 u t _33218)). Qed.
Lemma lem3238422 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : (term186 _84841 u t _33218) = (term186 _84841 u t _33218).
Proof. exact (eq_refl (term186 _84841 u t _33218)). Qed.
Lemma lem3238423 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : ((term80 _84841 t u _33218) = (term186 _84841 u t _33218)) = ((term186 _84841 u t _33218) = (term186 _84841 u t _33218)).
Proof. exact (MK_COMB (@lem3238416 _84841 u t _33218) (@lem3238422 _84841 u t _33218)). Qed.
Lemma lem3238425 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3238426 (x : Prop) : (x = x) = True.
Proof. exact (@lem3238425 Prop x). Qed.
Lemma lem3238427 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : ((term186 _84841 u t _33218) = (term186 _84841 u t _33218)) = True.
Proof. exact (@lem3238426 (term186 _84841 u t _33218)). Qed.
Lemma lem3238428 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : ((term80 _84841 t u _33218) = (term186 _84841 u t _33218)) = True.
Proof. exact (TRANS (@lem3238423 _84841 u t _33218) (@lem3238427 _84841 u t _33218)). Qed.
Lemma lem3238429 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : True = ((term80 _84841 t u _33218) = (term186 _84841 u t _33218)).
Proof. exact (SYM (@lem3238428 _84841 u t _33218)). Qed.
Lemma lem3238430 {_84841 : Type'} (u : _84841 -> Prop) (t : _84841 -> Prop) (_33218 : _84841) : (term80 _84841 t u _33218) = (term186 _84841 u t _33218).
Proof. exact (EQ_MP (@lem3238429 _84841 u t _33218) (@lem0)). Qed.
Lemma lem3238431 {_84841 : Type'} (_33218 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term186 _84841 u t _33218.
Proof. exact (EQ_MP (@lem3238430 _84841 u t _33218) (@lem3238163 _84841 _33218 x s t u h1)). Qed.
Lemma lem3238433 (b : Prop) (a : Prop) : (a \/ b) = (term189 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3238434 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (_33218 : _84841) : (term186 _84841 u t _33218) = (term190 _84841 t u _33218).
Proof. exact (@lem3238433 (term179 _84841 t _33218) (u _33218)). Qed.
Lemma lem3238436 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3238437 {_84841 : Type'} (t : _84841 -> Prop) (_33218 : _84841) : (term191 _84841 t _33218) = (t _33218).
Proof. exact (@lem3238436 (t _33218)). Qed.
Lemma lem3238438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3238439 {_84841 : Type'} (t : _84841 -> Prop) (_33218 : _84841) : (term192 _84841 t _33218) = (term35 _84841 t _33218).
Proof. exact (MK_COMB (@lem3238438) (@lem3238437 _84841 t _33218)). Qed.
Lemma lem3238440 {_84841 : Type'} (u : _84841 -> Prop) (_33218 : _84841) : (u _33218) = (u _33218).
Proof. exact (eq_refl (u _33218)). Qed.
Lemma lem3238441 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (_33218 : _84841) : (term190 _84841 t u _33218) = (term37 _84841 t u _33218).
Proof. exact (MK_COMB (@lem3238439 _84841 t _33218) (@lem3238440 _84841 u _33218)). Qed.
Lemma lem3238442 {_84841 : Type'} (t : _84841 -> Prop) (u : _84841 -> Prop) (_33218 : _84841) : (term186 _84841 u t _33218) = (term37 _84841 t u _33218).
Proof. exact (TRANS (@lem3238434 _84841 t u _33218) (@lem3238441 _84841 t u _33218)). Qed.
Lemma lem3238445 {_84841 : Type'} (_33218 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term37 _84841 t u _33218.
Proof. exact (EQ_MP (@lem3238442 _84841 t u _33218) (@lem3238431 _84841 _33218 x s t u h1)). Qed.
Lemma lem3238446 {_84841 : Type'} (_33218 : _84841) (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term37 _84841 t u _33218.
Proof. exact (@lem3238445 _84841 _33218 x s t u h1). Qed.
Lemma lem3238447 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term37 _84841 t u x.
Proof. exact (@lem3238446 _84841 x x s t u h1). Qed.
Lemma lem3238450 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : u x.
Proof. exact (@lem3238447 _84841 x s t u h2 (@lem3238402 _84841 t x h1)). Qed.
Lemma lem3238451 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : term184 _84841 u x.
Proof. exact (fun h0 : term179 _84841 u x => @lem3238450 _84841 x s t u h1 h2). Qed.
Lemma lem3238453 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238454 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term184 _84841 u x) = (u x).
Proof. exact (@lem3238453 (u x)). Qed.
Lemma lem3238455 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : u x.
Proof. exact (EQ_MP (@lem3238454 _84841 u x) (@lem3238451 _84841 x s t u h1 h2)). Qed.
Lemma lem3238458 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3238460 {_84841 : Type'} (u : _84841 -> Prop) (x : _84841) : (term179 _84841 u x) = (term193 _84841 u x).
Proof. exact (@lem3238458 (u x)). Qed.
Lemma lem3238463 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : term193 _84841 u x.
Proof. exact (EQ_MP (@lem3238460 _84841 u x) (@lem3238165 _84841 x s t u h1)). Qed.
Lemma lem3238466 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (@lem3238463 _84841 x s t u h2 (@lem3238455 _84841 x s t u h1 h2)). Qed.
Lemma lem3238467 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : term194.
Proof. exact (fun h0 : ~ False => @lem3238466 _84841 x s t u h1 h2). Qed.
Lemma lem3238469 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3238470 : term194 = False.
Proof. exact (@lem3238469 False). Qed.
Lemma lem3238471 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238470) (@lem3238467 _84841 x s t u h1 h2)). Qed.
Lemma lem3238472 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3238471 _84841 x s t u h1 h2) (fun h3 : False => @lem3238167 _84841 t x h1)). Qed.
Lemma lem3238473 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238472 _84841 x s t u h1 h2) (@lem3238167 _84841 t x h1)). Qed.
Lemma lem3238474 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3238395 _84841 x s t u h1 h2) (fun h3 : False => @lem3238151 _84841 s x h1)). Qed.
Lemma lem3238475 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238474 _84841 x s t u h1 h2) (@lem3238151 _84841 s x h1)). Qed.
Lemma lem3238476 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3238473 _84841 x s t u h1 h2) (fun h3 : False => @lem3238081 _84841 t x h1)). Qed.
Lemma lem3238477 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238476 _84841 x s t u h1 h2) (@lem3238081 _84841 t x h1)). Qed.
Lemma lem3238478 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3238475 _84841 x s t u h1 h2) (fun h3 : False => @lem3238047 _84841 s x h1)). Qed.
Lemma lem3238479 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238478 _84841 x s t u h1 h2) (@lem3238047 _84841 s x h1)). Qed.
Lemma lem3238480 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3238477 _84841 x s t u h1 h2) (fun h3 : False => @lem3238081 _84841 t x h1)). Qed.
Lemma lem3238481 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : t x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238480 _84841 x s t u h1 h2) (@lem3238081 _84841 t x h1)). Qed.
Lemma lem3238482 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3238479 _84841 x s t u h1 h2) (fun h3 : False => @lem3238047 _84841 s x h1)). Qed.
Lemma lem3238483 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : s x) (h2 : term155 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238482 _84841 x s t u h1 h2) (@lem3238047 _84841 s x h1)). Qed.
Lemma lem3238484 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term155 _84841 x s t u) : False.
Proof. exact (or_elim (@lem3237949 _84841 x s t u h1) (fun h0 : s x => @lem3238483 _84841 x s t u h0 h1) (fun h0 : t x => @lem3238481 _84841 x s t u h0 h1)). Qed.
Lemma lem3238485 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (x : _84841) (h1 : term137 _84841 s t u x) : False.
Proof. exact (or_elim (@lem3237936 _84841 s t u x h1) (fun h0 : term79 _84841 s u x => @lem3238243 _84841 t s u x h1 h0) (fun h0 : term79 _84841 t u x => @lem3238319 _84841 s t u x h1 h0)). Qed.
Lemma lem3238486 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term174 _84841 x s t u) : False.
Proof. exact (or_elim (@lem3237933 _84841 x s t u h1) (fun h0 : term137 _84841 s t u x => @lem3238485 _84841 s t u x h0) (fun h0 : term155 _84841 x s t u => @lem3238484 _84841 x s t u h0)). Qed.
Lemma lem3238487 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term174 _84841 x s t u) : (term174 _84841 x s t u) = False.
Proof. exact (prop_ext (fun h2 : term174 _84841 x s t u => @lem3238486 _84841 x s t u h1) (fun h2 : False => @lem3237933 _84841 x s t u h1)). Qed.
Lemma lem3238488 {_84841 : Type'} (x : _84841) (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term174 _84841 x s t u) : False.
Proof. exact (EQ_MP (@lem3238487 _84841 x s t u h1) (@lem3237933 _84841 x s t u h1)). Qed.
Lemma lem3238489 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term58 _84841 s t u) : False.
Proof. exact (ex_elim (@lem3237827 _84841 s t u h1) (fun x : _84841 => fun h0 : term176 _84841 s t u x => @lem3238488 _84841 x s t u h0)). Qed.
Lemma lem3238490 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term58 _84841 s t u) : (term58 _84841 s t u) = False.
Proof. exact (prop_ext (fun h2 : term58 _84841 s t u => @lem3238489 _84841 s t u h1) (fun h2 : False => @lem3237408 _84841 s t u h1)). Qed.
Lemma lem3238491 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) (h1 : term58 _84841 s t u) : False.
Proof. exact (EQ_MP (@lem3238490 _84841 s t u h1) (@lem3237408 _84841 s t u h1)). Qed.
Lemma lem3238492 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : term57 _84841 s t u.
Proof. exact (fun h0 : term58 _84841 s t u => @lem3238491 _84841 s t u h0). Qed.
Lemma lem3238493 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term32 _84841 s t u) = (term42 _84841 s t u).
Proof. exact (EQ_MP (@lem3237407 _84841 s t u) (@lem3238492 _84841 s t u)). Qed.
Lemma lem3238498 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : term44 _84841 s t.
Proof. exact (fun u : _84841 -> Prop => @lem3238493 _84841 s t u). Qed.
Lemma lem3238503 {_84841 : Type'} (s : _84841 -> Prop) : term46 _84841 s.
Proof. exact (fun t : _84841 -> Prop => @lem3238498 _84841 s t). Qed.
Lemma lem3238508 {_84841 : Type'} : term48 _84841.
Proof. exact (fun s : _84841 -> Prop => @lem3238503 _84841 s). Qed.
Lemma lem3238509 {_84841 : Type'} : term50 _84841.
Proof. exact (EQ_MP (@lem3237403 _84841) (@lem3238508 _84841)). Qed.
Lemma lem3238511 {_84841 : Type'} : term50 _84841.
Proof. exact (@lem3237265 _84841 (@lem3238509 _84841)). Qed.
Lemma lem3238512 {_84841 : Type'} (h1 : term51 _84841) : False.
Proof. exact (@lem3238511 _84841 (@lem3237249 _84841 h1)). Qed.
Lemma lem3238513 {_84841 : Type'} (h1 : term51 _84841) : (term51 _84841) = False.
Proof. exact (prop_ext (fun h2 : term51 _84841 => @lem3238512 _84841 h1) (fun h2 : False => @lem3237249 _84841 h1)). Qed.
Lemma lem3238514 {_84841 : Type'} (h1 : term51 _84841) : False.
Proof. exact (EQ_MP (@lem3238513 _84841 h1) (@lem3237249 _84841 h1)). Qed.
Lemma lem3238515 {_84841 : Type'} : term50 _84841.
Proof. exact (fun h0 : term51 _84841 => @lem3238514 _84841 h0). Qed.
Lemma lem3238516 {_84841 : Type'} : term48 _84841.
Proof. exact (EQ_MP (@lem3237248 _84841) (@lem3238515 _84841)). Qed.
Lemma lem3238517 {_84841 : Type'} : term20 _84841.
Proof. exact (EQ_MP (@lem3237244 _84841) (@lem3238516 _84841)). Qed.
Lemma lem3238518 {_84841 : Type'} : term19 _84841.
Proof. exact (EQ_MP (@lem3237103 _84841) (@lem3238517 _84841)). Qed.
