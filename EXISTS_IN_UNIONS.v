Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_IN_UNIONS_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Lemma lem3326953 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3326954 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3326955 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3326954 t1) (@lem3326953 t1)). Qed.
Lemma lem3326956 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3326955 t1 t2). Qed.
Lemma lem3326957 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3326958 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3326957 t1 t2) (@lem3326956 t1 t2)). Qed.
Lemma lem3326959 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3326958 t1 t2 t3). Qed.
Lemma lem3326960 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3326961 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3326960 t1 t2 t3) (@lem3326959 t1 t2 t3)). Qed.
Lemma lem3326962 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3326961 t1 t2 t3)). Qed.
Lemma lem3327012 {A : Type'} (s : type686 A) (x : A) : (term7 A x s) = (term8 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3327013 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term7 _86925 x s) = (term8 _86925 s x).
Proof. exact (@lem3327012 _86925 s x). Qed.
Lemma lem3327021 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3327022 {_86925 : Type'} (P : type686 _86925) (x : _86925 -> Prop) : (@IN (_86925 -> Prop) x P) = (P x).
Proof. exact (@lem3327021 (_86925 -> Prop) P x). Qed.
Lemma lem3327023 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (@IN (_86925 -> Prop) t s) = (s t).
Proof. exact (@lem3327022 _86925 s t). Qed.
Lemma lem3327024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327025 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term9 _86925 t s) = (term10 _86925 s t).
Proof. exact (MK_COMB (@lem3327024) (@lem3327023 _86925 s t)). Qed.
Lemma lem3327027 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3327028 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (@IN _86925 x P) = (P x).
Proof. exact (@lem3327027 _86925 P x). Qed.
Lemma lem3327029 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (@IN _86925 x t) = (t x).
Proof. exact (@lem3327028 _86925 t x). Qed.
Lemma lem3327030 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term11 _86925 s x t) = (term12 _86925 s t x).
Proof. exact (MK_COMB (@lem3327025 _86925 s t) (@lem3327029 _86925 t x)). Qed.
Lemma lem3327033 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term13 _86925 s x) = (term14 _86925 s x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327030 _86925 s t x)). Qed.
Lemma lem3327034 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327035 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term8 _86925 s x) = (term15 _86925 s x).
Proof. exact (MK_COMB (@lem3327034 _86925) (@lem3327033 _86925 s x)). Qed.
Lemma lem3327040 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term7 _86925 x s) = (term15 _86925 s x).
Proof. exact (TRANS (@lem3327013 _86925 s x) (@lem3327035 _86925 s x)). Qed.
Lemma lem3327041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327042 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term16 _86925 x s) = (term17 _86925 s x).
Proof. exact (MK_COMB (@lem3327041) (@lem3327040 _86925 s x)). Qed.
Lemma lem3327043 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3327044 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term18 _86925 s P x) = (term19 _86925 s P x).
Proof. exact (MK_COMB (@lem3327042 _86925 s x) (@lem3327043 _86925 P x)). Qed.
Lemma lem3327047 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term20 _86925 s P) = (term21 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327044 _86925 s P x)). Qed.
Lemma lem3327048 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327049 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term22 _86925 s P) = (term23 _86925 s P).
Proof. exact (MK_COMB (@lem3327048 _86925) (@lem3327047 _86925 s P)). Qed.
Lemma lem3327054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327055 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term24 _86925 s P) = (term25 _86925 s P).
Proof. exact (MK_COMB (@lem3327054) (@lem3327049 _86925 s P)). Qed.
Lemma lem3327067 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3327068 {_86925 : Type'} (P : type686 _86925) (x : _86925 -> Prop) : (@IN (_86925 -> Prop) x P) = (P x).
Proof. exact (@lem3327067 (_86925 -> Prop) P x). Qed.
Lemma lem3327069 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (@IN (_86925 -> Prop) t s) = (s t).
Proof. exact (@lem3327068 _86925 s t). Qed.
Lemma lem3327070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327071 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term9 _86925 t s) = (term10 _86925 s t).
Proof. exact (MK_COMB (@lem3327070) (@lem3327069 _86925 s t)). Qed.
Lemma lem3327075 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3327076 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (@IN _86925 x P) = (P x).
Proof. exact (@lem3327075 _86925 P x). Qed.
Lemma lem3327077 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (@IN _86925 x t) = (t x).
Proof. exact (@lem3327076 _86925 t x). Qed.
Lemma lem3327078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327079 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (term26 _86925 x t) = (term27 _86925 t x).
Proof. exact (MK_COMB (@lem3327078) (@lem3327077 _86925 t x)). Qed.
Lemma lem3327080 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3327081 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term28 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (MK_COMB (@lem3327079 _86925 t x) (@lem3327080 _86925 P x)). Qed.
Lemma lem3327084 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term30 _86925 s t P x) = (term31 _86925 s t P x).
Proof. exact (MK_COMB (@lem3327071 _86925 s t) (@lem3327081 _86925 t P x)). Qed.
Lemma lem3327087 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term32 _86925 s t P) = (term33 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327084 _86925 s t P x)). Qed.
Lemma lem3327088 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327089 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term34 _86925 s t P) = (term35 _86925 s t P).
Proof. exact (MK_COMB (@lem3327088 _86925) (@lem3327087 _86925 s t P)). Qed.
Lemma lem3327094 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term36 _86925 s P) = (term37 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327089 _86925 s t P)). Qed.
Lemma lem3327095 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327096 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term38 _86925 s P) = (term39 _86925 s P).
Proof. exact (MK_COMB (@lem3327095 _86925) (@lem3327094 _86925 s P)). Qed.
Lemma lem3327101 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : ((term22 _86925 s P) = (term38 _86925 s P)) = ((term23 _86925 s P) = (term39 _86925 s P)).
Proof. exact (MK_COMB (@lem3327055 _86925 s P) (@lem3327096 _86925 s P)). Qed.
Lemma lem3327104 {_86925 : Type'} (P : _86925 -> Prop) : (term40 _86925 P) = (term41 _86925 P).
Proof. exact (fun_ext (fun s : type686 _86925 => @lem3327101 _86925 s P)). Qed.
Lemma lem3327105 {_86925 : Type'} : (@all ((_86925 -> Prop) -> Prop)) = (@all ((_86925 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86925 -> Prop) -> Prop))). Qed.
Lemma lem3327106 {_86925 : Type'} (P : _86925 -> Prop) : (term42 _86925 P) = (term43 _86925 P).
Proof. exact (MK_COMB (@lem3327105 _86925) (@lem3327104 _86925 P)). Qed.
Lemma lem3327111 {_86925 : Type'} : (term44 _86925) = (term45 _86925).
Proof. exact (fun_ext (fun P : _86925 -> Prop => @lem3327106 _86925 P)). Qed.
Lemma lem3327112 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3327113 {_86925 : Type'} : (term46 _86925) = (term47 _86925).
Proof. exact (MK_COMB (@lem3327112 _86925) (@lem3327111 _86925)). Qed.
Lemma lem3327118 {_86925 : Type'} : (term47 _86925) = (term46 _86925).
Proof. exact (SYM (@lem3327113 _86925)). Qed.
Lemma lem3327120 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3327121 {_86925 : Type'} : (term47 _86925) = (term49 _86925).
Proof. exact (@lem3327120 (term47 _86925)). Qed.
Lemma lem3327122 {_86925 : Type'} : (term49 _86925) = (term47 _86925).
Proof. exact (SYM (@lem3327121 _86925)). Qed.
Lemma lem3327123 {_86925 : Type'} (h1 : term50 _86925) : term50 _86925.
Proof. exact (h1). Qed.
Lemma lem3327126 {_86925 : Type'} (h1 : term49 _86925) : term49 _86925.
Proof. exact (h1). Qed.
Lemma lem3327127 {_86925 : Type'} : term51 _86925.
Proof. exact (fun h0 : term49 _86925 => @lem3327126 _86925 h0). Qed.
Lemma lem3327128 {_86925 : Type'} (h1 : term51 _86925) : term51 _86925.
Proof. exact (h1). Qed.
Lemma lem3327129 {_86925 : Type'} (h1 : term49 _86925) : term49 _86925.
Proof. exact (h1). Qed.
Lemma lem3327130 {_86925 : Type'} (h1 : term49 _86925) (h2 : term51 _86925) : term49 _86925.
Proof. exact (@lem3327128 _86925 h2 (@lem3327129 _86925 h1)). Qed.
Lemma lem3327131 {_86925 : Type'} (h1 : term49 _86925) : term52 _86925.
Proof. exact (fun h0 : term51 _86925 => @lem3327130 _86925 h1 h0). Qed.
Lemma lem3327132 {_86925 : Type'} (h1 : term51 _86925) : term51 _86925.
Proof. exact (h1). Qed.
Lemma lem3327133 {_86925 : Type'} (h1 : term49 _86925) (h2 : term51 _86925) : term49 _86925.
Proof. exact (@lem3327131 _86925 h1 (@lem3327132 _86925 h2)). Qed.
Lemma lem3327134 {_86925 : Type'} (h1 : term51 _86925) : term51 _86925.
Proof. exact (fun h0 : term49 _86925 => @lem3327133 _86925 h0 h1). Qed.
Lemma lem3327135 {_86925 : Type'} : term53 _86925.
Proof. exact (fun h0 : term51 _86925 => @lem3327134 _86925 h0). Qed.
Lemma lem3327138 {_86925 : Type'} : term51 _86925.
Proof. exact (@lem3327135 _86925 (@lem3327127 _86925)). Qed.
Lemma lem3327139 {_86925 : Type'} : term51 _86925.
Proof. exact (@lem3327138 _86925). Qed.
Lemma lem3327141 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3327142 {_86925 : Type'} : (term49 _86925) = (term54 _86925).
Proof. exact (@lem3327141 (term50 _86925)). Qed.
Lemma lem3327144 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3327145 {_86925 : Type'} : (term54 _86925) = (term47 _86925).
Proof. exact (@lem3327144 (term47 _86925)). Qed.
Lemma lem3327150 {_86925 : Type'} : (term49 _86925) = (term47 _86925).
Proof. exact (TRANS (@lem3327142 _86925) (@lem3327145 _86925)). Qed.
Lemma lem3327224 {A : Type'} (P : Prop) (Q : A -> Prop) : (term56 A P Q) = (term57 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem3327225 {_86925 : Type'} (P : Prop) (Q : _86925 -> Prop) : (term56 _86925 P Q) = (term57 _86925 P Q).
Proof. exact (@lem3327224 _86925 P Q). Qed.
Lemma lem3327226 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term58 _86925 s t P) = (term59 _86925 s t P).
Proof. exact (@lem3327225 _86925 (s t) (term60 _86925 t P)). Qed.
Lemma lem3327227 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term61 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (eq_refl (term61 _86925 t P x)). Qed.
Lemma lem3327228 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term10 _86925 s t).
Proof. exact (eq_refl (term10 _86925 s t)). Qed.
Lemma lem3327229 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term62 _86925 s t P x) = (term31 _86925 s t P x).
Proof. exact (MK_COMB (@lem3327228 _86925 s t) (@lem3327227 _86925 t P x)). Qed.
Lemma lem3327230 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term63 _86925 s t P) = (term33 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327229 _86925 s t P x)). Qed.
Lemma lem3327231 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327232 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term58 _86925 s t P) = (term35 _86925 s t P).
Proof. exact (MK_COMB (@lem3327231 _86925) (@lem3327230 _86925 s t P)). Qed.
Lemma lem3327233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327234 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term64 _86925 s t P) = (term65 _86925 s t P).
Proof. exact (MK_COMB (@lem3327233) (@lem3327232 _86925 s t P)). Qed.
Lemma lem3327235 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term61 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (eq_refl (term61 _86925 t P x)). Qed.
Lemma lem3327236 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term66 _86925 t P) = (term60 _86925 t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327235 _86925 t P x)). Qed.
Lemma lem3327237 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327238 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term67 _86925 t P) = (term68 _86925 t P).
Proof. exact (MK_COMB (@lem3327237 _86925) (@lem3327236 _86925 t P)). Qed.
Lemma lem3327239 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term10 _86925 s t).
Proof. exact (eq_refl (term10 _86925 s t)). Qed.
Lemma lem3327240 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term59 _86925 s t P) = (term69 _86925 s t P).
Proof. exact (MK_COMB (@lem3327239 _86925 s t) (@lem3327238 _86925 t P)). Qed.
Lemma lem3327241 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : ((term58 _86925 s t P) = (term59 _86925 s t P)) = ((term35 _86925 s t P) = (term69 _86925 s t P)).
Proof. exact (MK_COMB (@lem3327234 _86925 s t P) (@lem3327240 _86925 s t P)). Qed.
Lemma lem3327242 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term35 _86925 s t P) = (term69 _86925 s t P).
Proof. exact (EQ_MP (@lem3327241 _86925 s t P) (@lem3327226 _86925 s t P)). Qed.
Lemma lem3327259 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term37 _86925 s P) = (term70 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327242 _86925 s t P)). Qed.
Lemma lem3327260 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327261 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term39 _86925 s P) = (term71 _86925 s P).
Proof. exact (MK_COMB (@lem3327260 _86925) (@lem3327259 _86925 s P)). Qed.
Lemma lem3327290 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term25 _86925 s P) = (term25 _86925 s P).
Proof. exact (eq_refl (term25 _86925 s P)). Qed.
Lemma lem3327291 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : ((term23 _86925 s P) = (term39 _86925 s P)) = ((term23 _86925 s P) = (term71 _86925 s P)).
Proof. exact (MK_COMB (@lem3327290 _86925 s P) (@lem3327261 _86925 s P)). Qed.
Lemma lem3327292 {_86925 : Type'} (P : _86925 -> Prop) : (term41 _86925 P) = (term72 _86925 P).
Proof. exact (fun_ext (fun s : type686 _86925 => @lem3327291 _86925 s P)). Qed.
Lemma lem3327293 {_86925 : Type'} : (@all ((_86925 -> Prop) -> Prop)) = (@all ((_86925 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86925 -> Prop) -> Prop))). Qed.
Lemma lem3327294 {_86925 : Type'} (P : _86925 -> Prop) : (term43 _86925 P) = (term73 _86925 P).
Proof. exact (MK_COMB (@lem3327293 _86925) (@lem3327292 _86925 P)). Qed.
Lemma lem3327299 {_86925 : Type'} : (term45 _86925) = (term74 _86925).
Proof. exact (fun_ext (fun P : _86925 -> Prop => @lem3327294 _86925 P)). Qed.
Lemma lem3327300 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3327301 {_86925 : Type'} : (term47 _86925) = (term75 _86925).
Proof. exact (MK_COMB (@lem3327300 _86925) (@lem3327299 _86925)). Qed.
Lemma lem3327310 {_86925 : Type'} : (term49 _86925) = (term75 _86925).
Proof. exact (TRANS (@lem3327150 _86925) (@lem3327301 _86925)). Qed.
Lemma lem3327315 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term29 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (eq_refl (term29 _86925 t P x)). Qed.
Lemma lem3327316 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term60 _86925 t P) = (term60 _86925 t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327315 _86925 t P x)). Qed.
Lemma lem3327317 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327318 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term68 _86925 t P) = (term68 _86925 t P).
Proof. exact (MK_COMB (@lem3327317 _86925) (@lem3327316 _86925 t P)). Qed.
Lemma lem3327321 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term10 _86925 s t).
Proof. exact (eq_refl (term10 _86925 s t)). Qed.
Lemma lem3327322 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term69 _86925 s t P) = (term69 _86925 s t P).
Proof. exact (MK_COMB (@lem3327321 _86925 s t) (@lem3327318 _86925 t P)). Qed.
Lemma lem3327323 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term70 _86925 s P) = (term70 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327322 _86925 s t P)). Qed.
Lemma lem3327324 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327325 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term71 _86925 s P) = (term71 _86925 s P).
Proof. exact (MK_COMB (@lem3327324 _86925) (@lem3327323 _86925 s P)). Qed.
Lemma lem3327326 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3327331 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term12 _86925 s t x) = (term12 _86925 s t x).
Proof. exact (eq_refl (term12 _86925 s t x)). Qed.
Lemma lem3327332 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term14 _86925 s x) = (term14 _86925 s x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327331 _86925 s t x)). Qed.
Lemma lem3327333 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327334 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term15 _86925 s x) = (term15 _86925 s x).
Proof. exact (MK_COMB (@lem3327333 _86925) (@lem3327332 _86925 s x)). Qed.
Lemma lem3327335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327336 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term17 _86925 s x) = (term17 _86925 s x).
Proof. exact (MK_COMB (@lem3327335) (@lem3327334 _86925 s x)). Qed.
Lemma lem3327337 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term19 _86925 s P x) = (term19 _86925 s P x).
Proof. exact (MK_COMB (@lem3327336 _86925 s x) (@lem3327326 _86925 P x)). Qed.
Lemma lem3327338 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term21 _86925 s P) = (term21 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327337 _86925 s P x)). Qed.
Lemma lem3327339 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327340 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term23 _86925 s P) = (term23 _86925 s P).
Proof. exact (MK_COMB (@lem3327339 _86925) (@lem3327338 _86925 s P)). Qed.
Lemma lem3327341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327342 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term25 _86925 s P) = (term25 _86925 s P).
Proof. exact (MK_COMB (@lem3327341) (@lem3327340 _86925 s P)). Qed.
Lemma lem3327343 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : ((term23 _86925 s P) = (term71 _86925 s P)) = ((term23 _86925 s P) = (term71 _86925 s P)).
Proof. exact (MK_COMB (@lem3327342 _86925 s P) (@lem3327325 _86925 s P)). Qed.
Lemma lem3327344 {_86925 : Type'} (P : _86925 -> Prop) : (term72 _86925 P) = (term72 _86925 P).
Proof. exact (fun_ext (fun s : type686 _86925 => @lem3327343 _86925 s P)). Qed.
Lemma lem3327345 {_86925 : Type'} : (@all ((_86925 -> Prop) -> Prop)) = (@all ((_86925 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86925 -> Prop) -> Prop))). Qed.
Lemma lem3327346 {_86925 : Type'} (P : _86925 -> Prop) : (term73 _86925 P) = (term73 _86925 P).
Proof. exact (MK_COMB (@lem3327345 _86925) (@lem3327344 _86925 P)). Qed.
Lemma lem3327347 {_86925 : Type'} : (term74 _86925) = (term74 _86925).
Proof. exact (fun_ext (fun P : _86925 -> Prop => @lem3327346 _86925 P)). Qed.
Lemma lem3327348 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3327349 {_86925 : Type'} : (term75 _86925) = (term75 _86925).
Proof. exact (MK_COMB (@lem3327348 _86925) (@lem3327347 _86925)). Qed.
Lemma lem3327396 {_86925 : Type'} : (term49 _86925) = (term75 _86925).
Proof. exact (TRANS (@lem3327310 _86925) (@lem3327349 _86925)). Qed.
Lemma lem3327397 {_86925 : Type'} : (term75 _86925) = (term49 _86925).
Proof. exact (SYM (@lem3327396 _86925)). Qed.
Lemma lem3327399 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3327400 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : ((term23 _86925 s P) = (term71 _86925 s P)) = (term76 _86925 s P).
Proof. exact (@lem3327399 ((term23 _86925 s P) = (term71 _86925 s P))). Qed.
Lemma lem3327401 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term76 _86925 s P) = ((term23 _86925 s P) = (term71 _86925 s P)).
Proof. exact (SYM (@lem3327400 _86925 s P)). Qed.
Lemma lem3327402 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (h1 : term77 _86925 s P) : term77 _86925 s P.
Proof. exact (h1). Qed.
Lemma lem3327411 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term78 _86925 s t x) = (term79 _86925 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3327414 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term12 _86925 s t x) = (term12 _86925 s t x).
Proof. exact (eq_refl (term12 _86925 s t x)). Qed.
Lemma lem3327415 {_86925 : Type'} (P : type686 _86925) : (term80 _86925 P) = (term81 _86925 P).
Proof. exact (@lem18394 (_86925 -> Prop) P). Qed.
Lemma lem3327416 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term82 _86925 s x) = (term83 _86925 s x).
Proof. exact (@lem3327415 _86925 (term14 _86925 s x)). Qed.
Lemma lem3327417 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term84 _86925 s x t) = (term12 _86925 s t x).
Proof. exact (eq_refl (term84 _86925 s x t)). Qed.
Lemma lem3327418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3327419 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term85 _86925 s x t) = (term78 _86925 s t x).
Proof. exact (MK_COMB (@lem3327418) (@lem3327417 _86925 s t x)). Qed.
Lemma lem3327420 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term85 _86925 s x t) = (term79 _86925 s t x).
Proof. exact (TRANS (@lem3327419 _86925 s t x) (@lem3327411 _86925 s t x)). Qed.
Lemma lem3327421 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term86 _86925 s x) = (term87 _86925 s x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327420 _86925 s t x)). Qed.
Lemma lem3327422 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3327423 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term83 _86925 s x) = (term88 _86925 s x).
Proof. exact (MK_COMB (@lem3327422 _86925) (@lem3327421 _86925 s x)). Qed.
Lemma lem3327424 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term82 _86925 s x) = (term88 _86925 s x).
Proof. exact (TRANS (@lem3327416 _86925 s x) (@lem3327423 _86925 s x)). Qed.
Lemma lem3327425 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term14 _86925 s x) = (term14 _86925 s x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327414 _86925 s t x)). Qed.
Lemma lem3327426 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327427 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term15 _86925 s x) = (term15 _86925 s x).
Proof. exact (MK_COMB (@lem3327426 _86925) (@lem3327425 _86925 s x)). Qed.
Lemma lem3327428 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (term89 _86925 P x) = (term89 _86925 P x).
Proof. exact (eq_refl (term89 _86925 P x)). Qed.
Lemma lem3327429 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3327430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3327431 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term90 _86925 s x) = (term91 _86925 s x).
Proof. exact (MK_COMB (@lem3327430) (@lem3327424 _86925 s x)). Qed.
Lemma lem3327432 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term92 _86925 s P x) = (term93 _86925 s P x).
Proof. exact (MK_COMB (@lem3327431 _86925 s x) (@lem3327428 _86925 P x)). Qed.
Lemma lem3327433 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term94 _86925 s P x) = (term92 _86925 s P x).
Proof. exact (@lem17045 (term15 _86925 s x) (P x)). Qed.
Lemma lem3327434 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term94 _86925 s P x) = (term93 _86925 s P x).
Proof. exact (TRANS (@lem3327433 _86925 s P x) (@lem3327432 _86925 s P x)). Qed.
Lemma lem3327435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327436 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term17 _86925 s x) = (term17 _86925 s x).
Proof. exact (MK_COMB (@lem3327435) (@lem3327427 _86925 s x)). Qed.
Lemma lem3327437 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term19 _86925 s P x) = (term19 _86925 s P x).
Proof. exact (MK_COMB (@lem3327436 _86925 s x) (@lem3327429 _86925 P x)). Qed.
Lemma lem3327438 {_86925 : Type'} (P : _86925 -> Prop) : (term95 _86925 P) = (term96 _86925 P).
Proof. exact (@lem18394 _86925 P). Qed.
Lemma lem3327439 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term97 _86925 s P) = (term98 _86925 s P).
Proof. exact (@lem3327438 _86925 (term21 _86925 s P)). Qed.
Lemma lem3327440 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term99 _86925 s P x) = (term19 _86925 s P x).
Proof. exact (eq_refl (term99 _86925 s P x)). Qed.
Lemma lem3327441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3327442 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term100 _86925 s P x) = (term94 _86925 s P x).
Proof. exact (MK_COMB (@lem3327441) (@lem3327440 _86925 s P x)). Qed.
Lemma lem3327443 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term100 _86925 s P x) = (term93 _86925 s P x).
Proof. exact (TRANS (@lem3327442 _86925 s P x) (@lem3327434 _86925 s P x)). Qed.
Lemma lem3327444 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term101 _86925 s P) = (term102 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327443 _86925 s P x)). Qed.
Lemma lem3327445 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3327446 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term98 _86925 s P) = (term103 _86925 s P).
Proof. exact (MK_COMB (@lem3327445 _86925) (@lem3327444 _86925 s P)). Qed.
Lemma lem3327447 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term97 _86925 s P) = (term103 _86925 s P).
Proof. exact (TRANS (@lem3327439 _86925 s P) (@lem3327446 _86925 s P)). Qed.
Lemma lem3327448 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term21 _86925 s P) = (term21 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327437 _86925 s P x)). Qed.
Lemma lem3327449 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327450 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term23 _86925 s P) = (term23 _86925 s P).
Proof. exact (MK_COMB (@lem3327449 _86925) (@lem3327448 _86925 s P)). Qed.
Lemma lem3327461 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term104 _86925 t P x) = (term105 _86925 t P x).
Proof. exact (@lem17045 (t x) (P x)). Qed.
Lemma lem3327464 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term29 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (eq_refl (term29 _86925 t P x)). Qed.
Lemma lem3327465 {_86925 : Type'} (P : _86925 -> Prop) : (term95 _86925 P) = (term96 _86925 P).
Proof. exact (@lem18394 _86925 P). Qed.
Lemma lem3327466 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term106 _86925 t P) = (term107 _86925 t P).
Proof. exact (@lem3327465 _86925 (term60 _86925 t P)). Qed.
Lemma lem3327467 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term61 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (eq_refl (term61 _86925 t P x)). Qed.
Lemma lem3327468 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3327469 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term108 _86925 t P x) = (term104 _86925 t P x).
Proof. exact (MK_COMB (@lem3327468) (@lem3327467 _86925 t P x)). Qed.
Lemma lem3327470 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term108 _86925 t P x) = (term105 _86925 t P x).
Proof. exact (TRANS (@lem3327469 _86925 t P x) (@lem3327461 _86925 t P x)). Qed.
Lemma lem3327471 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term109 _86925 t P) = (term110 _86925 t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327470 _86925 t P x)). Qed.
Lemma lem3327472 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3327473 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term107 _86925 t P) = (term111 _86925 t P).
Proof. exact (MK_COMB (@lem3327472 _86925) (@lem3327471 _86925 t P)). Qed.
Lemma lem3327474 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term106 _86925 t P) = (term111 _86925 t P).
Proof. exact (TRANS (@lem3327466 _86925 t P) (@lem3327473 _86925 t P)). Qed.
Lemma lem3327475 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term60 _86925 t P) = (term60 _86925 t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327464 _86925 t P x)). Qed.
Lemma lem3327476 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327477 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term68 _86925 t P) = (term68 _86925 t P).
Proof. exact (MK_COMB (@lem3327476 _86925) (@lem3327475 _86925 t P)). Qed.
Lemma lem3327479 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term112 _86925 s t) = (term112 _86925 s t).
Proof. exact (eq_refl (term112 _86925 s t)). Qed.
Lemma lem3327480 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term113 _86925 s t P) = (term114 _86925 s t P).
Proof. exact (MK_COMB (@lem3327479 _86925 s t) (@lem3327474 _86925 t P)). Qed.
Lemma lem3327481 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term115 _86925 s t P) = (term113 _86925 s t P).
Proof. exact (@lem17045 (s t) (term68 _86925 t P)). Qed.
Lemma lem3327482 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term115 _86925 s t P) = (term114 _86925 s t P).
Proof. exact (TRANS (@lem3327481 _86925 s t P) (@lem3327480 _86925 s t P)). Qed.
Lemma lem3327484 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term10 _86925 s t).
Proof. exact (eq_refl (term10 _86925 s t)). Qed.
Lemma lem3327485 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term69 _86925 s t P) = (term69 _86925 s t P).
Proof. exact (MK_COMB (@lem3327484 _86925 s t) (@lem3327477 _86925 t P)). Qed.
Lemma lem3327486 {_86925 : Type'} (P : type686 _86925) : (term80 _86925 P) = (term81 _86925 P).
Proof. exact (@lem18394 (_86925 -> Prop) P). Qed.
Lemma lem3327487 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term116 _86925 s P) = (term117 _86925 s P).
Proof. exact (@lem3327486 _86925 (term70 _86925 s P)). Qed.
Lemma lem3327488 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term118 _86925 s P t) = (term69 _86925 s t P).
Proof. exact (eq_refl (term118 _86925 s P t)). Qed.
Lemma lem3327489 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3327490 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term119 _86925 s P t) = (term115 _86925 s t P).
Proof. exact (MK_COMB (@lem3327489) (@lem3327488 _86925 s t P)). Qed.
Lemma lem3327491 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term119 _86925 s P t) = (term114 _86925 s t P).
Proof. exact (TRANS (@lem3327490 _86925 s t P) (@lem3327482 _86925 s t P)). Qed.
Lemma lem3327492 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term120 _86925 s P) = (term121 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327491 _86925 s t P)). Qed.
Lemma lem3327493 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3327494 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term117 _86925 s P) = (term122 _86925 s P).
Proof. exact (MK_COMB (@lem3327493 _86925) (@lem3327492 _86925 s P)). Qed.
Lemma lem3327495 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term116 _86925 s P) = (term122 _86925 s P).
Proof. exact (TRANS (@lem3327487 _86925 s P) (@lem3327494 _86925 s P)). Qed.
Lemma lem3327496 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term70 _86925 s P) = (term70 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327485 _86925 s t P)). Qed.
Lemma lem3327497 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327498 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term71 _86925 s P) = (term71 _86925 s P).
Proof. exact (MK_COMB (@lem3327497 _86925) (@lem3327496 _86925 s P)). Qed.
Lemma lem3327499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327500 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term123 _86925 s P) = (term124 _86925 s P).
Proof. exact (MK_COMB (@lem3327499) (@lem3327447 _86925 s P)). Qed.
Lemma lem3327501 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term125 _86925 s P) = (term126 _86925 s P).
Proof. exact (MK_COMB (@lem3327500 _86925 s P) (@lem3327498 _86925 s P)). Qed.
Lemma lem3327502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327503 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term127 _86925 s P) = (term127 _86925 s P).
Proof. exact (MK_COMB (@lem3327502) (@lem3327450 _86925 s P)). Qed.
Lemma lem3327504 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term128 _86925 s P) = (term129 _86925 s P).
Proof. exact (MK_COMB (@lem3327503 _86925 s P) (@lem3327495 _86925 s P)). Qed.
Lemma lem3327505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3327506 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term130 _86925 s P) = (term131 _86925 s P).
Proof. exact (MK_COMB (@lem3327505) (@lem3327504 _86925 s P)). Qed.
Lemma lem3327507 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term132 _86925 s P) = (term133 _86925 s P).
Proof. exact (MK_COMB (@lem3327506 _86925 s P) (@lem3327501 _86925 s P)). Qed.
Lemma lem3327508 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term77 _86925 s P) = (term132 _86925 s P).
Proof. exact (@lem17646 (term23 _86925 s P) (term71 _86925 s P)). Qed.
Lemma lem3327509 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term77 _86925 s P) = (term133 _86925 s P).
Proof. exact (TRANS (@lem3327508 _86925 s P) (@lem3327507 _86925 s P)). Qed.
Lemma lem3327804 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3327805 {_86925 : Type'} (P : type686 _86925) (Q : Prop) : (term136 _86925 P Q) = (term137 _86925 P Q).
Proof. exact (@lem3327804 (_86925 -> Prop) P Q). Qed.
Lemma lem3327806 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term138 _86925 s P x) = (term139 _86925 s P x).
Proof. exact (@lem3327805 _86925 (term14 _86925 s x) (P x)). Qed.
Lemma lem3327807 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term84 _86925 s x t) = (term12 _86925 s t x).
Proof. exact (eq_refl (term84 _86925 s x t)). Qed.
Lemma lem3327808 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term140 _86925 s x) = (term14 _86925 s x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327807 _86925 s t x)). Qed.
Lemma lem3327809 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327810 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term141 _86925 s x) = (term15 _86925 s x).
Proof. exact (MK_COMB (@lem3327809 _86925) (@lem3327808 _86925 s x)). Qed.
Lemma lem3327811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327812 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term142 _86925 s x) = (term17 _86925 s x).
Proof. exact (MK_COMB (@lem3327811) (@lem3327810 _86925 s x)). Qed.
Lemma lem3327813 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3327814 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term138 _86925 s P x) = (term19 _86925 s P x).
Proof. exact (MK_COMB (@lem3327812 _86925 s x) (@lem3327813 _86925 P x)). Qed.
Lemma lem3327815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327816 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term143 _86925 s P x) = (term144 _86925 s P x).
Proof. exact (MK_COMB (@lem3327815) (@lem3327814 _86925 s P x)). Qed.
Lemma lem3327817 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term84 _86925 s x t) = (term12 _86925 s t x).
Proof. exact (eq_refl (term84 _86925 s x t)). Qed.
Lemma lem3327818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327819 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term145 _86925 s x t) = (term146 _86925 s t x).
Proof. exact (MK_COMB (@lem3327818) (@lem3327817 _86925 s t x)). Qed.
Lemma lem3327820 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3327821 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term147 _86925 s t P x) = (term148 _86925 s t P x).
Proof. exact (MK_COMB (@lem3327819 _86925 s t x) (@lem3327820 _86925 P x)). Qed.
Lemma lem3327822 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term149 _86925 s P x) = (term150 _86925 s P x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327821 _86925 s t P x)). Qed.
Lemma lem3327823 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327824 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term139 _86925 s P x) = (term151 _86925 s P x).
Proof. exact (MK_COMB (@lem3327823 _86925) (@lem3327822 _86925 s P x)). Qed.
Lemma lem3327825 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : ((term138 _86925 s P x) = (term139 _86925 s P x)) = ((term19 _86925 s P x) = (term151 _86925 s P x)).
Proof. exact (MK_COMB (@lem3327816 _86925 s P x) (@lem3327824 _86925 s P x)). Qed.
Lemma lem3327826 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term19 _86925 s P x) = (term151 _86925 s P x).
Proof. exact (EQ_MP (@lem3327825 _86925 s P x) (@lem3327806 _86925 s P x)). Qed.
Lemma lem3327827 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term21 _86925 s P) = (term152 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327826 _86925 s P x)). Qed.
Lemma lem3327828 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327829 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term23 _86925 s P) = (term153 _86925 s P).
Proof. exact (MK_COMB (@lem3327828 _86925) (@lem3327827 _86925 s P)). Qed.
Lemma lem3327830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327831 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term127 _86925 s P) = (term154 _86925 s P).
Proof. exact (MK_COMB (@lem3327830) (@lem3327829 _86925 s P)). Qed.
Lemma lem3327832 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term122 _86925 s P) = (term122 _86925 s P).
Proof. exact (eq_refl (term122 _86925 s P)). Qed.
Lemma lem3327833 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term129 _86925 s P) = (term155 _86925 s P).
Proof. exact (MK_COMB (@lem3327831 _86925 s P) (@lem3327832 _86925 s P)). Qed.
Lemma lem3327835 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3327836 {_86925 : Type'} (P : _86925 -> Prop) (Q : Prop) : (term134 _86925 P Q) = (term135 _86925 P Q).
Proof. exact (@lem3327835 _86925 P Q). Qed.
Lemma lem3327837 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term156 _86925 s P) = (term157 _86925 s P).
Proof. exact (@lem3327836 _86925 (term152 _86925 s P) (term122 _86925 s P)). Qed.
Lemma lem3327838 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term158 _86925 s P x) = (term151 _86925 s P x).
Proof. exact (eq_refl (term158 _86925 s P x)). Qed.
Lemma lem3327839 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term159 _86925 s P) = (term152 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327838 _86925 s P x)). Qed.
Lemma lem3327840 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327841 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term160 _86925 s P) = (term153 _86925 s P).
Proof. exact (MK_COMB (@lem3327840 _86925) (@lem3327839 _86925 s P)). Qed.
Lemma lem3327842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327843 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term161 _86925 s P) = (term154 _86925 s P).
Proof. exact (MK_COMB (@lem3327842) (@lem3327841 _86925 s P)). Qed.
Lemma lem3327844 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term122 _86925 s P) = (term122 _86925 s P).
Proof. exact (eq_refl (term122 _86925 s P)). Qed.
Lemma lem3327845 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term156 _86925 s P) = (term155 _86925 s P).
Proof. exact (MK_COMB (@lem3327843 _86925 s P) (@lem3327844 _86925 s P)). Qed.
Lemma lem3327846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327847 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term162 _86925 s P) = (term163 _86925 s P).
Proof. exact (MK_COMB (@lem3327846) (@lem3327845 _86925 s P)). Qed.
Lemma lem3327848 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term158 _86925 s P x) = (term151 _86925 s P x).
Proof. exact (eq_refl (term158 _86925 s P x)). Qed.
Lemma lem3327849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327850 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term164 _86925 s P x) = (term165 _86925 s P x).
Proof. exact (MK_COMB (@lem3327849) (@lem3327848 _86925 s P x)). Qed.
Lemma lem3327851 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term122 _86925 s P) = (term122 _86925 s P).
Proof. exact (eq_refl (term122 _86925 s P)). Qed.
Lemma lem3327852 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term166 _86925 x s P) = (term167 _86925 x s P).
Proof. exact (MK_COMB (@lem3327850 _86925 s P x) (@lem3327851 _86925 s P)). Qed.
Lemma lem3327853 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term168 _86925 s P) = (term169 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327852 _86925 x s P)). Qed.
Lemma lem3327854 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327855 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term157 _86925 s P) = (term170 _86925 s P).
Proof. exact (MK_COMB (@lem3327854 _86925) (@lem3327853 _86925 s P)). Qed.
Lemma lem3327856 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : ((term156 _86925 s P) = (term157 _86925 s P)) = ((term155 _86925 s P) = (term170 _86925 s P)).
Proof. exact (MK_COMB (@lem3327847 _86925 s P) (@lem3327855 _86925 s P)). Qed.
Lemma lem3327857 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term155 _86925 s P) = (term170 _86925 s P).
Proof. exact (EQ_MP (@lem3327856 _86925 s P) (@lem3327837 _86925 s P)). Qed.
Lemma lem3327859 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3327860 {_86925 : Type'} (P : type686 _86925) (Q : Prop) : (term136 _86925 P Q) = (term137 _86925 P Q).
Proof. exact (@lem3327859 (_86925 -> Prop) P Q). Qed.
Lemma lem3327861 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term171 _86925 x s P) = (term172 _86925 x s P).
Proof. exact (@lem3327860 _86925 (term150 _86925 s P x) (term122 _86925 s P)). Qed.
Lemma lem3327862 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term173 _86925 s P x t) = (term148 _86925 s t P x).
Proof. exact (eq_refl (term173 _86925 s P x t)). Qed.
Lemma lem3327863 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term174 _86925 s P x) = (term150 _86925 s P x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327862 _86925 s t P x)). Qed.
Lemma lem3327864 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327865 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term175 _86925 s P x) = (term151 _86925 s P x).
Proof. exact (MK_COMB (@lem3327864 _86925) (@lem3327863 _86925 s P x)). Qed.
Lemma lem3327866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327867 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term176 _86925 s P x) = (term165 _86925 s P x).
Proof. exact (MK_COMB (@lem3327866) (@lem3327865 _86925 s P x)). Qed.
Lemma lem3327868 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term122 _86925 s P) = (term122 _86925 s P).
Proof. exact (eq_refl (term122 _86925 s P)). Qed.
Lemma lem3327869 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term171 _86925 x s P) = (term167 _86925 x s P).
Proof. exact (MK_COMB (@lem3327867 _86925 s P x) (@lem3327868 _86925 s P)). Qed.
Lemma lem3327870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327871 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term177 _86925 x s P) = (term178 _86925 x s P).
Proof. exact (MK_COMB (@lem3327870) (@lem3327869 _86925 x s P)). Qed.
Lemma lem3327872 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term173 _86925 s P x t) = (term148 _86925 s t P x).
Proof. exact (eq_refl (term173 _86925 s P x t)). Qed.
Lemma lem3327873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3327874 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term179 _86925 s P x t) = (term180 _86925 s t P x).
Proof. exact (MK_COMB (@lem3327873) (@lem3327872 _86925 s t P x)). Qed.
Lemma lem3327875 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term122 _86925 s P) = (term122 _86925 s P).
Proof. exact (eq_refl (term122 _86925 s P)). Qed.
Lemma lem3327876 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term181 _86925 x t s P) = (term182 _86925 t x s P).
Proof. exact (MK_COMB (@lem3327874 _86925 s t P x) (@lem3327875 _86925 s P)). Qed.
Lemma lem3327877 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term183 _86925 x s P) = (term184 _86925 x s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327876 _86925 t x s P)). Qed.
Lemma lem3327878 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327879 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term172 _86925 x s P) = (term185 _86925 x s P).
Proof. exact (MK_COMB (@lem3327878 _86925) (@lem3327877 _86925 x s P)). Qed.
Lemma lem3327880 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : ((term171 _86925 x s P) = (term172 _86925 x s P)) = ((term167 _86925 x s P) = (term185 _86925 x s P)).
Proof. exact (MK_COMB (@lem3327871 _86925 x s P) (@lem3327879 _86925 x s P)). Qed.
Lemma lem3327881 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term167 _86925 x s P) = (term185 _86925 x s P).
Proof. exact (EQ_MP (@lem3327880 _86925 x s P) (@lem3327861 _86925 x s P)). Qed.
Lemma lem3327882 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term169 _86925 s P) = (term186 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327881 _86925 x s P)). Qed.
Lemma lem3327883 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327884 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term170 _86925 s P) = (term187 _86925 s P).
Proof. exact (MK_COMB (@lem3327883 _86925) (@lem3327882 _86925 s P)). Qed.
Lemma lem3327885 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term155 _86925 s P) = (term187 _86925 s P).
Proof. exact (TRANS (@lem3327857 _86925 s P) (@lem3327884 _86925 s P)). Qed.
Lemma lem3327886 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term129 _86925 s P) = (term187 _86925 s P).
Proof. exact (TRANS (@lem3327833 _86925 s P) (@lem3327885 _86925 s P)). Qed.
Lemma lem3327887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3327888 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term131 _86925 s P) = (term188 _86925 s P).
Proof. exact (MK_COMB (@lem3327887) (@lem3327886 _86925 s P)). Qed.
Lemma lem3327890 {A : Type'} (P : Prop) (Q : A -> Prop) : (term57 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3327891 {_86925 : Type'} (P : Prop) (Q : _86925 -> Prop) : (term57 _86925 P Q) = (term56 _86925 P Q).
Proof. exact (@lem3327890 _86925 P Q). Qed.
Lemma lem3327892 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term59 _86925 s t P) = (term58 _86925 s t P).
Proof. exact (@lem3327891 _86925 (s t) (term60 _86925 t P)). Qed.
Lemma lem3327893 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term61 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (eq_refl (term61 _86925 t P x)). Qed.
Lemma lem3327894 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term66 _86925 t P) = (term60 _86925 t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327893 _86925 t P x)). Qed.
Lemma lem3327895 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327896 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term67 _86925 t P) = (term68 _86925 t P).
Proof. exact (MK_COMB (@lem3327895 _86925) (@lem3327894 _86925 t P)). Qed.
Lemma lem3327897 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term10 _86925 s t).
Proof. exact (eq_refl (term10 _86925 s t)). Qed.
Lemma lem3327898 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term59 _86925 s t P) = (term69 _86925 s t P).
Proof. exact (MK_COMB (@lem3327897 _86925 s t) (@lem3327896 _86925 t P)). Qed.
Lemma lem3327899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327900 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term189 _86925 s t P) = (term190 _86925 s t P).
Proof. exact (MK_COMB (@lem3327899) (@lem3327898 _86925 s t P)). Qed.
Lemma lem3327901 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term61 _86925 t P x) = (term29 _86925 t P x).
Proof. exact (eq_refl (term61 _86925 t P x)). Qed.
Lemma lem3327902 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term10 _86925 s t).
Proof. exact (eq_refl (term10 _86925 s t)). Qed.
Lemma lem3327903 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term62 _86925 s t P x) = (term31 _86925 s t P x).
Proof. exact (MK_COMB (@lem3327902 _86925 s t) (@lem3327901 _86925 t P x)). Qed.
Lemma lem3327904 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term63 _86925 s t P) = (term33 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327903 _86925 s t P x)). Qed.
Lemma lem3327905 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327906 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term58 _86925 s t P) = (term35 _86925 s t P).
Proof. exact (MK_COMB (@lem3327905 _86925) (@lem3327904 _86925 s t P)). Qed.
Lemma lem3327907 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : ((term59 _86925 s t P) = (term58 _86925 s t P)) = ((term69 _86925 s t P) = (term35 _86925 s t P)).
Proof. exact (MK_COMB (@lem3327900 _86925 s t P) (@lem3327906 _86925 s t P)). Qed.
Lemma lem3327908 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term69 _86925 s t P) = (term35 _86925 s t P).
Proof. exact (EQ_MP (@lem3327907 _86925 s t P) (@lem3327892 _86925 s t P)). Qed.
Lemma lem3327909 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term70 _86925 s P) = (term37 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327908 _86925 s t P)). Qed.
Lemma lem3327910 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327911 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term71 _86925 s P) = (term39 _86925 s P).
Proof. exact (MK_COMB (@lem3327910 _86925) (@lem3327909 _86925 s P)). Qed.
Lemma lem3327912 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term124 _86925 s P) = (term124 _86925 s P).
Proof. exact (eq_refl (term124 _86925 s P)). Qed.
Lemma lem3327913 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term126 _86925 s P) = (term191 _86925 s P).
Proof. exact (MK_COMB (@lem3327912 _86925 s P) (@lem3327911 _86925 s P)). Qed.
Lemma lem3327915 {A : Type'} (P : Prop) (Q : A -> Prop) : (term57 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3327916 {_86925 : Type'} (P : Prop) (Q : type686 _86925) : (term192 _86925 P Q) = (term193 _86925 P Q).
Proof. exact (@lem3327915 (_86925 -> Prop) P Q). Qed.
Lemma lem3327917 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term194 _86925 s P) = (term195 _86925 s P).
Proof. exact (@lem3327916 _86925 (term103 _86925 s P) (term37 _86925 s P)). Qed.
Lemma lem3327918 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term196 _86925 s P t) = (term35 _86925 s t P).
Proof. exact (eq_refl (term196 _86925 s P t)). Qed.
Lemma lem3327919 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term197 _86925 s P) = (term37 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327918 _86925 s t P)). Qed.
Lemma lem3327920 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327921 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term198 _86925 s P) = (term39 _86925 s P).
Proof. exact (MK_COMB (@lem3327920 _86925) (@lem3327919 _86925 s P)). Qed.
Lemma lem3327922 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term124 _86925 s P) = (term124 _86925 s P).
Proof. exact (eq_refl (term124 _86925 s P)). Qed.
Lemma lem3327923 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term194 _86925 s P) = (term191 _86925 s P).
Proof. exact (MK_COMB (@lem3327922 _86925 s P) (@lem3327921 _86925 s P)). Qed.
Lemma lem3327924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327925 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term199 _86925 s P) = (term200 _86925 s P).
Proof. exact (MK_COMB (@lem3327924) (@lem3327923 _86925 s P)). Qed.
Lemma lem3327926 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term196 _86925 s P t) = (term35 _86925 s t P).
Proof. exact (eq_refl (term196 _86925 s P t)). Qed.
Lemma lem3327927 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term124 _86925 s P) = (term124 _86925 s P).
Proof. exact (eq_refl (term124 _86925 s P)). Qed.
Lemma lem3327928 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term201 _86925 s P t) = (term202 _86925 s t P).
Proof. exact (MK_COMB (@lem3327927 _86925 s P) (@lem3327926 _86925 s t P)). Qed.
Lemma lem3327929 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term203 _86925 s P) = (term204 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327928 _86925 s t P)). Qed.
Lemma lem3327930 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327931 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term195 _86925 s P) = (term205 _86925 s P).
Proof. exact (MK_COMB (@lem3327930 _86925) (@lem3327929 _86925 s P)). Qed.
Lemma lem3327932 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : ((term194 _86925 s P) = (term195 _86925 s P)) = ((term191 _86925 s P) = (term205 _86925 s P)).
Proof. exact (MK_COMB (@lem3327925 _86925 s P) (@lem3327931 _86925 s P)). Qed.
Lemma lem3327933 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term191 _86925 s P) = (term205 _86925 s P).
Proof. exact (EQ_MP (@lem3327932 _86925 s P) (@lem3327917 _86925 s P)). Qed.
Lemma lem3327935 {A : Type'} (P : Prop) (Q : A -> Prop) : (term57 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3327936 {_86925 : Type'} (P : Prop) (Q : _86925 -> Prop) : (term57 _86925 P Q) = (term56 _86925 P Q).
Proof. exact (@lem3327935 _86925 P Q). Qed.
Lemma lem3327937 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term206 _86925 s t P) = (term207 _86925 s t P).
Proof. exact (@lem3327936 _86925 (term103 _86925 s P) (term33 _86925 s t P)). Qed.
Lemma lem3327938 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term208 _86925 s t P x) = (term31 _86925 s t P x).
Proof. exact (eq_refl (term208 _86925 s t P x)). Qed.
Lemma lem3327939 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term209 _86925 s t P) = (term33 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327938 _86925 s t P x)). Qed.
Lemma lem3327940 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327941 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term210 _86925 s t P) = (term35 _86925 s t P).
Proof. exact (MK_COMB (@lem3327940 _86925) (@lem3327939 _86925 s t P)). Qed.
Lemma lem3327942 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term124 _86925 s P) = (term124 _86925 s P).
Proof. exact (eq_refl (term124 _86925 s P)). Qed.
Lemma lem3327943 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term206 _86925 s t P) = (term202 _86925 s t P).
Proof. exact (MK_COMB (@lem3327942 _86925 s P) (@lem3327941 _86925 s t P)). Qed.
Lemma lem3327944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327945 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term211 _86925 s t P) = (term212 _86925 s t P).
Proof. exact (MK_COMB (@lem3327944) (@lem3327943 _86925 s t P)). Qed.
Lemma lem3327946 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term208 _86925 s t P x) = (term31 _86925 s t P x).
Proof. exact (eq_refl (term208 _86925 s t P x)). Qed.
Lemma lem3327947 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term124 _86925 s P) = (term124 _86925 s P).
Proof. exact (eq_refl (term124 _86925 s P)). Qed.
Lemma lem3327948 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term213 _86925 s t P x) = (term214 _86925 s t P x).
Proof. exact (MK_COMB (@lem3327947 _86925 s P) (@lem3327946 _86925 s t P x)). Qed.
Lemma lem3327949 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term215 _86925 s t P) = (term216 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327948 _86925 s t P x)). Qed.
Lemma lem3327950 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327951 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term207 _86925 s t P) = (term217 _86925 s t P).
Proof. exact (MK_COMB (@lem3327950 _86925) (@lem3327949 _86925 s t P)). Qed.
Lemma lem3327952 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : ((term206 _86925 s t P) = (term207 _86925 s t P)) = ((term202 _86925 s t P) = (term217 _86925 s t P)).
Proof. exact (MK_COMB (@lem3327945 _86925 s t P) (@lem3327951 _86925 s t P)). Qed.
Lemma lem3327953 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term202 _86925 s t P) = (term217 _86925 s t P).
Proof. exact (EQ_MP (@lem3327952 _86925 s t P) (@lem3327937 _86925 s t P)). Qed.
Lemma lem3327954 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term204 _86925 s P) = (term218 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327953 _86925 s t P)). Qed.
Lemma lem3327955 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327956 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term205 _86925 s P) = (term219 _86925 s P).
Proof. exact (MK_COMB (@lem3327955 _86925) (@lem3327954 _86925 s P)). Qed.
Lemma lem3327957 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term191 _86925 s P) = (term219 _86925 s P).
Proof. exact (TRANS (@lem3327933 _86925 s P) (@lem3327956 _86925 s P)). Qed.
Lemma lem3327958 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term126 _86925 s P) = (term219 _86925 s P).
Proof. exact (TRANS (@lem3327913 _86925 s P) (@lem3327957 _86925 s P)). Qed.
Lemma lem3327959 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term133 _86925 s P) = (term220 _86925 s P).
Proof. exact (MK_COMB (@lem3327888 _86925 s P) (@lem3327958 _86925 s P)). Qed.
Lemma lem3327963 {A : Type'} (P : A -> Prop) (Q : Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3327964 {_86925 : Type'} (P : _86925 -> Prop) (Q : Prop) : (term221 _86925 P Q) = (term222 _86925 P Q).
Proof. exact (@lem3327963 _86925 P Q). Qed.
Lemma lem3327965 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term223 _86925 s P) = (term224 _86925 s P).
Proof. exact (@lem3327964 _86925 (term186 _86925 s P) (term219 _86925 s P)). Qed.
Lemma lem3327966 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term225 _86925 s P x) = (term185 _86925 x s P).
Proof. exact (eq_refl (term225 _86925 s P x)). Qed.
Lemma lem3327967 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term226 _86925 s P) = (term186 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327966 _86925 x s P)). Qed.
Lemma lem3327968 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327969 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term227 _86925 s P) = (term187 _86925 s P).
Proof. exact (MK_COMB (@lem3327968 _86925) (@lem3327967 _86925 s P)). Qed.
Lemma lem3327970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3327971 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term228 _86925 s P) = (term188 _86925 s P).
Proof. exact (MK_COMB (@lem3327970) (@lem3327969 _86925 s P)). Qed.
Lemma lem3327972 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term219 _86925 s P) = (term219 _86925 s P).
Proof. exact (eq_refl (term219 _86925 s P)). Qed.
Lemma lem3327973 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term223 _86925 s P) = (term220 _86925 s P).
Proof. exact (MK_COMB (@lem3327971 _86925 s P) (@lem3327972 _86925 s P)). Qed.
Lemma lem3327974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3327975 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term229 _86925 s P) = (term230 _86925 s P).
Proof. exact (MK_COMB (@lem3327974) (@lem3327973 _86925 s P)). Qed.
Lemma lem3327976 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term225 _86925 s P x) = (term185 _86925 x s P).
Proof. exact (eq_refl (term225 _86925 s P x)). Qed.
Lemma lem3327977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3327978 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term231 _86925 s P x) = (term232 _86925 x s P).
Proof. exact (MK_COMB (@lem3327977) (@lem3327976 _86925 x s P)). Qed.
Lemma lem3327979 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term219 _86925 s P) = (term219 _86925 s P).
Proof. exact (eq_refl (term219 _86925 s P)). Qed.
Lemma lem3327980 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term233 _86925 x s P) = (term234 _86925 x s P).
Proof. exact (MK_COMB (@lem3327978 _86925 x s P) (@lem3327979 _86925 s P)). Qed.
Lemma lem3327981 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term235 _86925 s P) = (term236 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3327980 _86925 x s P)). Qed.
Lemma lem3327982 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3327983 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term224 _86925 s P) = (term237 _86925 s P).
Proof. exact (MK_COMB (@lem3327982 _86925) (@lem3327981 _86925 s P)). Qed.
Lemma lem3327984 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : ((term223 _86925 s P) = (term224 _86925 s P)) = ((term220 _86925 s P) = (term237 _86925 s P)).
Proof. exact (MK_COMB (@lem3327975 _86925 s P) (@lem3327983 _86925 s P)). Qed.
Lemma lem3327985 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term220 _86925 s P) = (term237 _86925 s P).
Proof. exact (EQ_MP (@lem3327984 _86925 s P) (@lem3327965 _86925 s P)). Qed.
Lemma lem3327987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3327988 {_86925 : Type'} (P : type686 _86925) (Q : type686 _86925) : (term240 _86925 P Q) = (term241 _86925 P Q).
Proof. exact (@lem3327987 (_86925 -> Prop) P Q). Qed.
Lemma lem3327989 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term242 _86925 x s P) = (term243 _86925 x s P).
Proof. exact (@lem3327988 _86925 (term184 _86925 x s P) (term218 _86925 s P)). Qed.
Lemma lem3327990 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term244 _86925 x s P t) = (term182 _86925 t x s P).
Proof. exact (eq_refl (term244 _86925 x s P t)). Qed.
Lemma lem3327991 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term245 _86925 x s P) = (term184 _86925 x s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327990 _86925 t x s P)). Qed.
Lemma lem3327992 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327993 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term246 _86925 x s P) = (term185 _86925 x s P).
Proof. exact (MK_COMB (@lem3327992 _86925) (@lem3327991 _86925 x s P)). Qed.
Lemma lem3327994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3327995 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term247 _86925 x s P) = (term232 _86925 x s P).
Proof. exact (MK_COMB (@lem3327994) (@lem3327993 _86925 x s P)). Qed.
Lemma lem3327996 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term248 _86925 s P t) = (term217 _86925 s t P).
Proof. exact (eq_refl (term248 _86925 s P t)). Qed.
Lemma lem3327997 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term249 _86925 s P) = (term218 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3327996 _86925 s t P)). Qed.
Lemma lem3327998 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3327999 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term250 _86925 s P) = (term219 _86925 s P).
Proof. exact (MK_COMB (@lem3327998 _86925) (@lem3327997 _86925 s P)). Qed.
Lemma lem3328000 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term242 _86925 x s P) = (term234 _86925 x s P).
Proof. exact (MK_COMB (@lem3327995 _86925 x s P) (@lem3327999 _86925 s P)). Qed.
Lemma lem3328001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328002 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term251 _86925 x s P) = (term252 _86925 x s P).
Proof. exact (MK_COMB (@lem3328001) (@lem3328000 _86925 x s P)). Qed.
Lemma lem3328003 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term244 _86925 x s P t) = (term182 _86925 t x s P).
Proof. exact (eq_refl (term244 _86925 x s P t)). Qed.
Lemma lem3328004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328005 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term253 _86925 x s P t) = (term254 _86925 t x s P).
Proof. exact (MK_COMB (@lem3328004) (@lem3328003 _86925 t x s P)). Qed.
Lemma lem3328006 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term248 _86925 s P t) = (term217 _86925 s t P).
Proof. exact (eq_refl (term248 _86925 s P t)). Qed.
Lemma lem3328007 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term255 _86925 x s P t) = (term256 _86925 x s t P).
Proof. exact (MK_COMB (@lem3328005 _86925 t x s P) (@lem3328006 _86925 s t P)). Qed.
Lemma lem3328008 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term257 _86925 x s P) = (term258 _86925 x s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328007 _86925 x s t P)). Qed.
Lemma lem3328009 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3328010 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term243 _86925 x s P) = (term259 _86925 x s P).
Proof. exact (MK_COMB (@lem3328009 _86925) (@lem3328008 _86925 x s P)). Qed.
Lemma lem3328011 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : ((term242 _86925 x s P) = (term243 _86925 x s P)) = ((term234 _86925 x s P) = (term259 _86925 x s P)).
Proof. exact (MK_COMB (@lem3328002 _86925 x s P) (@lem3328010 _86925 x s P)). Qed.
Lemma lem3328012 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term234 _86925 x s P) = (term259 _86925 x s P).
Proof. exact (EQ_MP (@lem3328011 _86925 x s P) (@lem3327989 _86925 x s P)). Qed.
Lemma lem3328014 {A : Type'} (P : Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3328015 {_86925 : Type'} (P : Prop) (Q : _86925 -> Prop) : (term260 _86925 P Q) = (term261 _86925 P Q).
Proof. exact (@lem3328014 _86925 P Q). Qed.
Lemma lem3328016 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term262 _86925 x s t P) = (term263 _86925 x s t P).
Proof. exact (@lem3328015 _86925 (term182 _86925 t x s P) (term216 _86925 s t P)). Qed.
Lemma lem3328017 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term264 _86925 s t P x) = (term214 _86925 s t P x).
Proof. exact (eq_refl (term264 _86925 s t P x)). Qed.
Lemma lem3328018 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term265 _86925 s t P) = (term216 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328017 _86925 s t P x)). Qed.
Lemma lem3328019 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3328020 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term266 _86925 s t P) = (term217 _86925 s t P).
Proof. exact (MK_COMB (@lem3328019 _86925) (@lem3328018 _86925 s t P)). Qed.
Lemma lem3328021 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term254 _86925 t x s P) = (term254 _86925 t x s P).
Proof. exact (eq_refl (term254 _86925 t x s P)). Qed.
Lemma lem3328022 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term262 _86925 x s t P) = (term256 _86925 x s t P).
Proof. exact (MK_COMB (@lem3328021 _86925 t x s P) (@lem3328020 _86925 s t P)). Qed.
Lemma lem3328023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328024 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term267 _86925 x s t P) = (term268 _86925 x s t P).
Proof. exact (MK_COMB (@lem3328023) (@lem3328022 _86925 x s t P)). Qed.
Lemma lem3328025 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) : (term264 _86925 s t P x') = (term214 _86925 s t P x').
Proof. exact (eq_refl (term264 _86925 s t P x')). Qed.
Lemma lem3328026 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term254 _86925 t x s P) = (term254 _86925 t x s P).
Proof. exact (eq_refl (term254 _86925 t x s P)). Qed.
Lemma lem3328027 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) : (term269 _86925 x s t P x') = (term270 _86925 x s t P x').
Proof. exact (MK_COMB (@lem3328026 _86925 t x s P) (@lem3328025 _86925 s t P x')). Qed.
Lemma lem3328028 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term271 _86925 x s t P) = (term272 _86925 x s t P).
Proof. exact (fun_ext (fun x' : _86925 => @lem3328027 _86925 x s t P x')). Qed.
Lemma lem3328029 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3328030 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term263 _86925 x s t P) = (term273 _86925 x s t P).
Proof. exact (MK_COMB (@lem3328029 _86925) (@lem3328028 _86925 x s t P)). Qed.
Lemma lem3328031 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : ((term262 _86925 x s t P) = (term263 _86925 x s t P)) = ((term256 _86925 x s t P) = (term273 _86925 x s t P)).
Proof. exact (MK_COMB (@lem3328024 _86925 x s t P) (@lem3328030 _86925 x s t P)). Qed.
Lemma lem3328032 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term256 _86925 x s t P) = (term273 _86925 x s t P).
Proof. exact (EQ_MP (@lem3328031 _86925 x s t P) (@lem3328016 _86925 x s t P)). Qed.
Lemma lem3328033 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term258 _86925 x s P) = (term274 _86925 x s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328032 _86925 x s t P)). Qed.
Lemma lem3328034 {_86925 : Type'} : (@ex (_86925 -> Prop)) = (@ex (_86925 -> Prop)).
Proof. exact (eq_refl (@ex (_86925 -> Prop))). Qed.
Lemma lem3328035 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term259 _86925 x s P) = (term275 _86925 x s P).
Proof. exact (MK_COMB (@lem3328034 _86925) (@lem3328033 _86925 x s P)). Qed.
Lemma lem3328036 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term234 _86925 x s P) = (term275 _86925 x s P).
Proof. exact (TRANS (@lem3328012 _86925 x s P) (@lem3328035 _86925 x s P)). Qed.
Lemma lem3328037 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term236 _86925 s P) = (term276 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328036 _86925 x s P)). Qed.
Lemma lem3328038 {_86925 : Type'} : (@ex _86925) = (@ex _86925).
Proof. exact (eq_refl (@ex _86925)). Qed.
Lemma lem3328039 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term237 _86925 s P) = (term277 _86925 s P).
Proof. exact (MK_COMB (@lem3328038 _86925) (@lem3328037 _86925 s P)). Qed.
Lemma lem3328040 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term220 _86925 s P) = (term277 _86925 s P).
Proof. exact (TRANS (@lem3327985 _86925 s P) (@lem3328039 _86925 s P)). Qed.
Lemma lem3328042 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term133 _86925 s P) = (term277 _86925 s P).
Proof. exact (TRANS (@lem3327959 _86925 s P) (@lem3328040 _86925 s P)). Qed.
Lemma lem3328043 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term77 _86925 s P) = (term277 _86925 s P).
Proof. exact (TRANS (@lem3327509 _86925 s P) (@lem3328042 _86925 s P)). Qed.
Lemma lem3328044 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (h1 : term77 _86925 s P) : term277 _86925 s P.
Proof. exact (EQ_MP (@lem3328043 _86925 s P) (@lem3327402 _86925 s P h1)). Qed.
Lemma lem3328045 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term275 _86925 x s P) : term275 _86925 x s P.
Proof. exact (h1). Qed.
Lemma lem3328046 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (h1 : term273 _86925 x s t P) : term273 _86925 x s t P.
Proof. exact (h1). Qed.
Lemma lem3328047 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term270 _86925 x s t P x') : term270 _86925 x s t P x'.
Proof. exact (h1). Qed.
Lemma lem3328052 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328053 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328052 _86925 Prop f x). Qed.
Lemma lem3328055 {_86925 : Type'} (P : _86925 -> Prop) (x' : _86925) : (P x') = (@I (_86925 -> Prop) P x').
Proof. exact (@lem3328053 _86925 P x'). Qed.
Lemma lem3328060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328061 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328060 _86925 Prop f x). Qed.
Lemma lem3328063 {_86925 : Type'} (t : _86925 -> Prop) (x' : _86925) : (t x') = (@I (_86925 -> Prop) t x').
Proof. exact (@lem3328061 _86925 t x'). Qed.
Lemma lem3328064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328065 {_86925 : Type'} (t : _86925 -> Prop) (x' : _86925) : (term27 _86925 t x') = (term278 _86925 t x').
Proof. exact (MK_COMB (@lem3328064) (@lem3328063 _86925 t x')). Qed.
Lemma lem3328066 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) : (term29 _86925 t P x') = (term279 _86925 t P x').
Proof. exact (MK_COMB (@lem3328065 _86925 t x') (@lem3328055 _86925 P x')). Qed.
Lemma lem3328071 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328072 {_86925 : Type'} (f : type686 _86925) (x : _86925 -> Prop) : (f x) = (@I ((_86925 -> Prop) -> Prop) f x).
Proof. exact (@lem3328071 (_86925 -> Prop) Prop f x). Qed.
Lemma lem3328074 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (s t) = (@I ((_86925 -> Prop) -> Prop) s t).
Proof. exact (@lem3328072 _86925 s t). Qed.
Lemma lem3328075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328076 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term280 _86925 s t).
Proof. exact (MK_COMB (@lem3328075) (@lem3328074 _86925 s t)). Qed.
Lemma lem3328077 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) : (term31 _86925 s t P x') = (term281 _86925 s t P x').
Proof. exact (MK_COMB (@lem3328076 _86925 s t) (@lem3328066 _86925 t P x')). Qed.
Lemma lem3328078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328084 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328083 _86925 Prop f x). Qed.
Lemma lem3328086 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (@I (_86925 -> Prop) P x).
Proof. exact (@lem3328084 _86925 P x). Qed.
Lemma lem3328087 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (term89 _86925 P x) = (term282 _86925 P x).
Proof. exact (MK_COMB (@lem3328078) (@lem3328086 _86925 P x)). Qed.
Lemma lem3328088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328094 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328093 _86925 Prop f x). Qed.
Lemma lem3328096 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (t x) = (@I (_86925 -> Prop) t x).
Proof. exact (@lem3328094 _86925 t x). Qed.
Lemma lem3328097 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (term89 _86925 t x) = (term282 _86925 t x).
Proof. exact (MK_COMB (@lem3328088) (@lem3328096 _86925 t x)). Qed.
Lemma lem3328098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328103 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328104 {_86925 : Type'} (f : type686 _86925) (x : _86925 -> Prop) : (f x) = (@I ((_86925 -> Prop) -> Prop) f x).
Proof. exact (@lem3328103 (_86925 -> Prop) Prop f x). Qed.
Lemma lem3328106 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (s t) = (@I ((_86925 -> Prop) -> Prop) s t).
Proof. exact (@lem3328104 _86925 s t). Qed.
Lemma lem3328107 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term283 _86925 s t) = (term284 _86925 s t).
Proof. exact (MK_COMB (@lem3328098) (@lem3328106 _86925 s t)). Qed.
Lemma lem3328108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328109 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term112 _86925 s t) = (term285 _86925 s t).
Proof. exact (MK_COMB (@lem3328108) (@lem3328107 _86925 s t)). Qed.
Lemma lem3328110 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term79 _86925 s t x) = (term286 _86925 s t x).
Proof. exact (MK_COMB (@lem3328109 _86925 s t) (@lem3328097 _86925 t x)). Qed.
Lemma lem3328111 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term87 _86925 s x) = (term287 _86925 s x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328110 _86925 s t x)). Qed.
Lemma lem3328112 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3328113 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term88 _86925 s x) = (term288 _86925 s x).
Proof. exact (MK_COMB (@lem3328112 _86925) (@lem3328111 _86925 s x)). Qed.
Lemma lem3328114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328115 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term91 _86925 s x) = (term289 _86925 s x).
Proof. exact (MK_COMB (@lem3328114) (@lem3328113 _86925 s x)). Qed.
Lemma lem3328116 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term93 _86925 s P x) = (term290 _86925 s P x).
Proof. exact (MK_COMB (@lem3328115 _86925 s x) (@lem3328087 _86925 P x)). Qed.
Lemma lem3328117 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term102 _86925 s P) = (term291 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328116 _86925 s P x)). Qed.
Lemma lem3328118 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3328119 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term103 _86925 s P) = (term292 _86925 s P).
Proof. exact (MK_COMB (@lem3328118 _86925) (@lem3328117 _86925 s P)). Qed.
Lemma lem3328120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328121 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term124 _86925 s P) = (term293 _86925 s P).
Proof. exact (MK_COMB (@lem3328120) (@lem3328119 _86925 s P)). Qed.
Lemma lem3328122 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) : (term214 _86925 s t P x') = (term294 _86925 s t P x').
Proof. exact (MK_COMB (@lem3328121 _86925 s P) (@lem3328077 _86925 s t P x')). Qed.
Lemma lem3328123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328129 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328128 _86925 Prop f x). Qed.
Lemma lem3328131 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (@I (_86925 -> Prop) P x).
Proof. exact (@lem3328129 _86925 P x). Qed.
Lemma lem3328132 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (term89 _86925 P x) = (term282 _86925 P x).
Proof. exact (MK_COMB (@lem3328123) (@lem3328131 _86925 P x)). Qed.
Lemma lem3328133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328138 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328139 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328138 _86925 Prop f x). Qed.
Lemma lem3328141 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (t x) = (@I (_86925 -> Prop) t x).
Proof. exact (@lem3328139 _86925 t x). Qed.
Lemma lem3328142 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (term89 _86925 t x) = (term282 _86925 t x).
Proof. exact (MK_COMB (@lem3328133) (@lem3328141 _86925 t x)). Qed.
Lemma lem3328143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328144 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (term295 _86925 t x) = (term296 _86925 t x).
Proof. exact (MK_COMB (@lem3328143) (@lem3328142 _86925 t x)). Qed.
Lemma lem3328145 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term105 _86925 t P x) = (term297 _86925 t P x).
Proof. exact (MK_COMB (@lem3328144 _86925 t x) (@lem3328132 _86925 P x)). Qed.
Lemma lem3328146 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term110 _86925 t P) = (term298 _86925 t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328145 _86925 t P x)). Qed.
Lemma lem3328147 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3328148 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term111 _86925 t P) = (term299 _86925 t P).
Proof. exact (MK_COMB (@lem3328147 _86925) (@lem3328146 _86925 t P)). Qed.
Lemma lem3328149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3328154 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328155 {_86925 : Type'} (f : type686 _86925) (x : _86925 -> Prop) : (f x) = (@I ((_86925 -> Prop) -> Prop) f x).
Proof. exact (@lem3328154 (_86925 -> Prop) Prop f x). Qed.
Lemma lem3328157 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (s t) = (@I ((_86925 -> Prop) -> Prop) s t).
Proof. exact (@lem3328155 _86925 s t). Qed.
Lemma lem3328158 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term283 _86925 s t) = (term284 _86925 s t).
Proof. exact (MK_COMB (@lem3328149) (@lem3328157 _86925 s t)). Qed.
Lemma lem3328159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328160 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term112 _86925 s t) = (term285 _86925 s t).
Proof. exact (MK_COMB (@lem3328159) (@lem3328158 _86925 s t)). Qed.
Lemma lem3328161 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term114 _86925 s t P) = (term300 _86925 s t P).
Proof. exact (MK_COMB (@lem3328160 _86925 s t) (@lem3328148 _86925 t P)). Qed.
Lemma lem3328162 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term121 _86925 s P) = (term301 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328161 _86925 s t P)). Qed.
Lemma lem3328163 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3328164 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term122 _86925 s P) = (term302 _86925 s P).
Proof. exact (MK_COMB (@lem3328163 _86925) (@lem3328162 _86925 s P)). Qed.
Lemma lem3328169 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328170 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328169 _86925 Prop f x). Qed.
Lemma lem3328172 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (P x) = (@I (_86925 -> Prop) P x).
Proof. exact (@lem3328170 _86925 P x). Qed.
Lemma lem3328177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328178 {_86925 : Type'} (f : _86925 -> Prop) (x : _86925) : (f x) = (@I (_86925 -> Prop) f x).
Proof. exact (@lem3328177 _86925 Prop f x). Qed.
Lemma lem3328180 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (t x) = (@I (_86925 -> Prop) t x).
Proof. exact (@lem3328178 _86925 t x). Qed.
Lemma lem3328185 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3328186 {_86925 : Type'} (f : type686 _86925) (x : _86925 -> Prop) : (f x) = (@I ((_86925 -> Prop) -> Prop) f x).
Proof. exact (@lem3328185 (_86925 -> Prop) Prop f x). Qed.
Lemma lem3328188 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (s t) = (@I ((_86925 -> Prop) -> Prop) s t).
Proof. exact (@lem3328186 _86925 s t). Qed.
Lemma lem3328189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328190 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term10 _86925 s t) = (term280 _86925 s t).
Proof. exact (MK_COMB (@lem3328189) (@lem3328188 _86925 s t)). Qed.
Lemma lem3328191 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term12 _86925 s t x) = (term303 _86925 s t x).
Proof. exact (MK_COMB (@lem3328190 _86925 s t) (@lem3328180 _86925 t x)). Qed.
Lemma lem3328192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328193 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term146 _86925 s t x) = (term304 _86925 s t x).
Proof. exact (MK_COMB (@lem3328192) (@lem3328191 _86925 s t x)). Qed.
Lemma lem3328194 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term148 _86925 s t P x) = (term305 _86925 s t P x).
Proof. exact (MK_COMB (@lem3328193 _86925 s t x) (@lem3328172 _86925 P x)). Qed.
Lemma lem3328195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3328196 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term180 _86925 s t P x) = (term306 _86925 s t P x).
Proof. exact (MK_COMB (@lem3328195) (@lem3328194 _86925 s t P x)). Qed.
Lemma lem3328197 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term182 _86925 t x s P) = (term307 _86925 t x s P).
Proof. exact (MK_COMB (@lem3328196 _86925 s t P x) (@lem3328164 _86925 s P)). Qed.
Lemma lem3328198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328199 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) : (term254 _86925 t x s P) = (term308 _86925 t x s P).
Proof. exact (MK_COMB (@lem3328198) (@lem3328197 _86925 t x s P)). Qed.
Lemma lem3328200 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) : (term270 _86925 x s t P x') = (term309 _86925 x s t P x').
Proof. exact (MK_COMB (@lem3328199 _86925 t x s P) (@lem3328122 _86925 s t P x')). Qed.
Lemma lem3328201 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term270 _86925 x s t P x') : term309 _86925 x s t P x'.
Proof. exact (EQ_MP (@lem3328200 _86925 x s t P x') (@lem3328047 _86925 x s t P x' h1)). Qed.
Lemma lem3328202 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term307 _86925 t x s P.
Proof. exact (h1). Qed.
Lemma lem3328203 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term294 _86925 s t P x'.
Proof. exact (h1). Qed.
Lemma lem3328204 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term302 _86925 s P.
Proof. exact (proj2 (@lem3328202 _86925 t x s P h1)). Qed.
Lemma lem3328205 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term305 _86925 s t P x.
Proof. exact (proj1 (@lem3328202 _86925 t x s P h1)). Qed.
Lemma lem3328207 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term303 _86925 s t x.
Proof. exact (proj1 (@lem3328205 _86925 t x s P h1)). Qed.
Lemma lem3328210 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term281 _86925 s t P x'.
Proof. exact (proj2 (@lem3328203 _86925 s t P x' h1)). Qed.
Lemma lem3328211 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term292 _86925 s P.
Proof. exact (proj1 (@lem3328203 _86925 s t P x' h1)). Qed.
Lemma lem3328212 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term279 _86925 t P x'.
Proof. exact (proj2 (@lem3328210 _86925 s t P x' h1)). Qed.
Lemma lem3328217 {A : Type'} (P : Prop) (Q : A -> Prop) : (term310 A P Q) = (term311 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3328218 {_86925 : Type'} (P : Prop) (Q : _86925 -> Prop) : (term310 _86925 P Q) = (term311 _86925 P Q).
Proof. exact (@lem3328217 _86925 P Q). Qed.
Lemma lem3328219 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term312 _86925 s t P) = (term313 _86925 s t P).
Proof. exact (@lem3328218 _86925 (term284 _86925 s t) (term298 _86925 t P)). Qed.
Lemma lem3328220 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term314 _86925 t P x) = (term297 _86925 t P x).
Proof. exact (eq_refl (term314 _86925 t P x)). Qed.
Lemma lem3328221 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term315 _86925 t P) = (term298 _86925 t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328220 _86925 t P x)). Qed.
Lemma lem3328222 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3328223 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) : (term316 _86925 t P) = (term299 _86925 t P).
Proof. exact (MK_COMB (@lem3328222 _86925) (@lem3328221 _86925 t P)). Qed.
Lemma lem3328224 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term285 _86925 s t) = (term285 _86925 s t).
Proof. exact (eq_refl (term285 _86925 s t)). Qed.
Lemma lem3328225 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term312 _86925 s t P) = (term300 _86925 s t P).
Proof. exact (MK_COMB (@lem3328224 _86925 s t) (@lem3328223 _86925 t P)). Qed.
Lemma lem3328226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328227 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term317 _86925 s t P) = (term318 _86925 s t P).
Proof. exact (MK_COMB (@lem3328226) (@lem3328225 _86925 s t P)). Qed.
Lemma lem3328228 {_86925 : Type'} (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term314 _86925 t P x) = (term297 _86925 t P x).
Proof. exact (eq_refl (term314 _86925 t P x)). Qed.
Lemma lem3328229 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term285 _86925 s t) = (term285 _86925 s t).
Proof. exact (eq_refl (term285 _86925 s t)). Qed.
Lemma lem3328230 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term319 _86925 s t P x) = (term320 _86925 s t P x).
Proof. exact (MK_COMB (@lem3328229 _86925 s t) (@lem3328228 _86925 t P x)). Qed.
Lemma lem3328231 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term321 _86925 s t P) = (term322 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328230 _86925 s t P x)). Qed.
Lemma lem3328232 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3328233 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term313 _86925 s t P) = (term323 _86925 s t P).
Proof. exact (MK_COMB (@lem3328232 _86925) (@lem3328231 _86925 s t P)). Qed.
Lemma lem3328234 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : ((term312 _86925 s t P) = (term313 _86925 s t P)) = ((term300 _86925 s t P) = (term323 _86925 s t P)).
Proof. exact (MK_COMB (@lem3328227 _86925 s t P) (@lem3328233 _86925 s t P)). Qed.
Lemma lem3328235 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term300 _86925 s t P) = (term323 _86925 s t P).
Proof. exact (EQ_MP (@lem3328234 _86925 s t P) (@lem3328219 _86925 s t P)). Qed.
Lemma lem3328236 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term301 _86925 s P) = (term324 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328235 _86925 s t P)). Qed.
Lemma lem3328237 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3328238 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term302 _86925 s P) = (term325 _86925 s P).
Proof. exact (MK_COMB (@lem3328237 _86925) (@lem3328236 _86925 s P)). Qed.
Lemma lem3328251 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term320 _86925 s t P x) = (term320 _86925 s t P x).
Proof. exact (eq_refl (term320 _86925 s t P x)). Qed.
Lemma lem3328252 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term322 _86925 s t P) = (term322 _86925 s t P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328251 _86925 s t P x)). Qed.
Lemma lem3328253 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3328254 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) : (term323 _86925 s t P) = (term323 _86925 s t P).
Proof. exact (MK_COMB (@lem3328253 _86925) (@lem3328252 _86925 s t P)). Qed.
Lemma lem3328255 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term324 _86925 s P) = (term324 _86925 s P).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328254 _86925 s t P)). Qed.
Lemma lem3328256 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3328257 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term325 _86925 s P) = (term325 _86925 s P).
Proof. exact (MK_COMB (@lem3328256 _86925) (@lem3328255 _86925 s P)). Qed.
Lemma lem3328258 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term302 _86925 s P) = (term325 _86925 s P).
Proof. exact (TRANS (@lem3328238 _86925 s P) (@lem3328257 _86925 s P)). Qed.
Lemma lem3328259 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term325 _86925 s P.
Proof. exact (EQ_MP (@lem3328258 _86925 s P) (@lem3328204 _86925 t x s P h1)). Qed.
Lemma lem3328273 {A : Type'} (P : A -> Prop) (Q : Prop) : (term326 A P Q) = (term327 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3328274 {_86925 : Type'} (P : type686 _86925) (Q : Prop) : (term328 _86925 P Q) = (term329 _86925 P Q).
Proof. exact (@lem3328273 (_86925 -> Prop) P Q). Qed.
Lemma lem3328275 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term330 _86925 s P x) = (term331 _86925 s P x).
Proof. exact (@lem3328274 _86925 (term287 _86925 s x) (term282 _86925 P x)). Qed.
Lemma lem3328276 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term332 _86925 s x t) = (term286 _86925 s t x).
Proof. exact (eq_refl (term332 _86925 s x t)). Qed.
Lemma lem3328277 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term333 _86925 s x) = (term287 _86925 s x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328276 _86925 s t x)). Qed.
Lemma lem3328278 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3328279 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term334 _86925 s x) = (term288 _86925 s x).
Proof. exact (MK_COMB (@lem3328278 _86925) (@lem3328277 _86925 s x)). Qed.
Lemma lem3328280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328281 {_86925 : Type'} (s : type686 _86925) (x : _86925) : (term335 _86925 s x) = (term289 _86925 s x).
Proof. exact (MK_COMB (@lem3328280) (@lem3328279 _86925 s x)). Qed.
Lemma lem3328282 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (term282 _86925 P x) = (term282 _86925 P x).
Proof. exact (eq_refl (term282 _86925 P x)). Qed.
Lemma lem3328283 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term330 _86925 s P x) = (term290 _86925 s P x).
Proof. exact (MK_COMB (@lem3328281 _86925 s x) (@lem3328282 _86925 P x)). Qed.
Lemma lem3328284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3328285 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term336 _86925 s P x) = (term337 _86925 s P x).
Proof. exact (MK_COMB (@lem3328284) (@lem3328283 _86925 s P x)). Qed.
Lemma lem3328286 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term332 _86925 s x t) = (term286 _86925 s t x).
Proof. exact (eq_refl (term332 _86925 s x t)). Qed.
Lemma lem3328287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3328288 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (x : _86925) : (term338 _86925 s x t) = (term339 _86925 s t x).
Proof. exact (MK_COMB (@lem3328287) (@lem3328286 _86925 s t x)). Qed.
Lemma lem3328289 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (term282 _86925 P x) = (term282 _86925 P x).
Proof. exact (eq_refl (term282 _86925 P x)). Qed.
Lemma lem3328290 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term340 _86925 s t P x) = (term341 _86925 s t P x).
Proof. exact (MK_COMB (@lem3328288 _86925 s t x) (@lem3328289 _86925 P x)). Qed.
Lemma lem3328291 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term342 _86925 s P x) = (term343 _86925 s P x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328290 _86925 s t P x)). Qed.
Lemma lem3328292 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3328293 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term331 _86925 s P x) = (term344 _86925 s P x).
Proof. exact (MK_COMB (@lem3328292 _86925) (@lem3328291 _86925 s P x)). Qed.
Lemma lem3328294 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : ((term330 _86925 s P x) = (term331 _86925 s P x)) = ((term290 _86925 s P x) = (term344 _86925 s P x)).
Proof. exact (MK_COMB (@lem3328285 _86925 s P x) (@lem3328293 _86925 s P x)). Qed.
Lemma lem3328295 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term290 _86925 s P x) = (term344 _86925 s P x).
Proof. exact (EQ_MP (@lem3328294 _86925 s P x) (@lem3328275 _86925 s P x)). Qed.
Lemma lem3328296 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term291 _86925 s P) = (term345 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328295 _86925 s P x)). Qed.
Lemma lem3328297 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3328298 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term292 _86925 s P) = (term346 _86925 s P).
Proof. exact (MK_COMB (@lem3328297 _86925) (@lem3328296 _86925 s P)). Qed.
Lemma lem3328311 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x : _86925) : (term341 _86925 s t P x) = (term341 _86925 s t P x).
Proof. exact (eq_refl (term341 _86925 s t P x)). Qed.
Lemma lem3328312 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term343 _86925 s P x) = (term343 _86925 s P x).
Proof. exact (fun_ext (fun t : _86925 -> Prop => @lem3328311 _86925 s t P x)). Qed.
Lemma lem3328313 {_86925 : Type'} : (@all (_86925 -> Prop)) = (@all (_86925 -> Prop)).
Proof. exact (eq_refl (@all (_86925 -> Prop))). Qed.
Lemma lem3328314 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (x : _86925) : (term344 _86925 s P x) = (term344 _86925 s P x).
Proof. exact (MK_COMB (@lem3328313 _86925) (@lem3328312 _86925 s P x)). Qed.
Lemma lem3328315 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term345 _86925 s P) = (term345 _86925 s P).
Proof. exact (fun_ext (fun x : _86925 => @lem3328314 _86925 s P x)). Qed.
Lemma lem3328316 {_86925 : Type'} : (@all _86925) = (@all _86925).
Proof. exact (eq_refl (@all _86925)). Qed.
Lemma lem3328317 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term346 _86925 s P) = (term346 _86925 s P).
Proof. exact (MK_COMB (@lem3328316 _86925) (@lem3328315 _86925 s P)). Qed.
Lemma lem3328318 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term292 _86925 s P) = (term346 _86925 s P).
Proof. exact (TRANS (@lem3328298 _86925 s P) (@lem3328317 _86925 s P)). Qed.
Lemma lem3328319 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term346 _86925 s P.
Proof. exact (EQ_MP (@lem3328318 _86925 s P) (@lem3328211 _86925 s t P x' h1)). Qed.
Lemma lem3328332 {_86925 : Type'} (_34533 : _86925 -> Prop) (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term347 _86925 s P _34533.
Proof. exact (@lem3328259 _86925 t x s P h1 _34533). Qed.
Lemma lem3328333 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) (P : _86925 -> Prop) : (term347 _86925 s P _34533) = (term323 _86925 s _34533 P).
Proof. exact (eq_refl (term347 _86925 s P _34533)). Qed.
Lemma lem3328334 {_86925 : Type'} (_34533 : _86925 -> Prop) (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term323 _86925 s _34533 P.
Proof. exact (EQ_MP (@lem3328333 _86925 s _34533 P) (@lem3328332 _86925 _34533 t x s P h1)). Qed.
Lemma lem3328335 {_86925 : Type'} (_34533 : _86925 -> Prop) (_34534 : _86925) (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term348 _86925 s _34533 P _34534.
Proof. exact (@lem3328334 _86925 _34533 t x s P h1 _34534). Qed.
Lemma lem3328336 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) (P : _86925 -> Prop) (_34534 : _86925) : (term348 _86925 s _34533 P _34534) = (term320 _86925 s _34533 P _34534).
Proof. exact (eq_refl (term348 _86925 s _34533 P _34534)). Qed.
Lemma lem3328338 {_86925 : Type'} (_34535 : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term349 _86925 s P _34535.
Proof. exact (@lem3328319 _86925 s t P x' h1 _34535). Qed.
Lemma lem3328339 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (_34535 : _86925) : (term349 _86925 s P _34535) = (term344 _86925 s P _34535).
Proof. exact (eq_refl (term349 _86925 s P _34535)). Qed.
Lemma lem3328340 {_86925 : Type'} (_34535 : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term344 _86925 s P _34535.
Proof. exact (EQ_MP (@lem3328339 _86925 s P _34535) (@lem3328338 _86925 _34535 s t P x' h1)). Qed.
Lemma lem3328341 {_86925 : Type'} (_34535 : _86925) (_34536 : _86925 -> Prop) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term350 _86925 s P _34535 _34536.
Proof. exact (@lem3328340 _86925 _34535 s t P x' h1 _34536). Qed.
Lemma lem3328342 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term350 _86925 s P _34535 _34536) = (term341 _86925 s _34536 P _34535).
Proof. exact (eq_refl (term350 _86925 s P _34535 _34536)). Qed.
Lemma lem3328343 {_86925 : Type'} (_34536 : _86925 -> Prop) (_34535 : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term341 _86925 s _34536 P _34535.
Proof. exact (EQ_MP (@lem3328342 _86925 s _34536 P _34535) (@lem3328341 _86925 _34535 _34536 s t P x' h1)). Qed.
Lemma lem3328353 {_86925 : Type'} (_34533 : _86925 -> Prop) (_34534 : _86925) (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term320 _86925 s _34533 P _34534.
Proof. exact (EQ_MP (@lem3328336 _86925 s _34533 P _34534) (@lem3328335 _86925 _34533 _34534 t x s P h1)). Qed.
Lemma lem3328370 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term341 _86925 s _34536 P _34535) = (term320 _86925 s _34536 P _34535).
Proof. exact (@lem3326962 (term284 _86925 s _34536) (term282 _86925 _34536 _34535) (term282 _86925 P _34535)). Qed.
Lemma lem3328371 {_86925 : Type'} (_34536 : _86925 -> Prop) (_34535 : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term320 _86925 s _34536 P _34535.
Proof. exact (EQ_MP (@lem3328370 _86925 s _34536 P _34535) (@lem3328343 _86925 _34536 _34535 s t P x' h1)). Qed.
Lemma lem3328379 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : @I ((_86925 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3328207 _86925 t x s P h1)). Qed.
Lemma lem3328380 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term351 _86925 s t.
Proof. exact (fun h0 : term284 _86925 s t => @lem3328379 _86925 t x s P h1). Qed.
Lemma lem3328382 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328383 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term351 _86925 s t) = (@I ((_86925 -> Prop) -> Prop) s t).
Proof. exact (@lem3328382 (@I ((_86925 -> Prop) -> Prop) s t)). Qed.
Lemma lem3328384 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : @I ((_86925 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3328383 _86925 s t) (@lem3328380 _86925 t x s P h1)). Qed.
Lemma lem3328386 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : @I (_86925 -> Prop) t x.
Proof. exact (proj2 (@lem3328207 _86925 t x s P h1)). Qed.
Lemma lem3328387 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term353 _86925 t x.
Proof. exact (fun h0 : term282 _86925 t x => @lem3328386 _86925 t x s P h1). Qed.
Lemma lem3328389 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328390 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) : (term353 _86925 t x) = (@I (_86925 -> Prop) t x).
Proof. exact (@lem3328389 (@I (_86925 -> Prop) t x)). Qed.
Lemma lem3328391 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : @I (_86925 -> Prop) t x.
Proof. exact (EQ_MP (@lem3328390 _86925 t x) (@lem3328387 _86925 t x s P h1)). Qed.
Lemma lem3328393 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : @I (_86925 -> Prop) P x.
Proof. exact (proj2 (@lem3328205 _86925 t x s P h1)). Qed.
Lemma lem3328394 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term353 _86925 P x.
Proof. exact (fun h0 : term282 _86925 P x => @lem3328393 _86925 t x s P h1). Qed.
Lemma lem3328396 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328397 {_86925 : Type'} (P : _86925 -> Prop) (x : _86925) : (term353 _86925 P x) = (@I (_86925 -> Prop) P x).
Proof. exact (@lem3328396 (@I (_86925 -> Prop) P x)). Qed.
Lemma lem3328398 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : @I (_86925 -> Prop) P x.
Proof. exact (EQ_MP (@lem3328397 _86925 P x) (@lem3328394 _86925 t x s P h1)). Qed.
Lemma lem3328400 (a : Prop) (b : Prop) : (term354 a b) = (term355 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3328401 {_86925 : Type'} (_34533 : _86925 -> Prop) (P : _86925 -> Prop) (_34534 : _86925) : (term297 _86925 _34533 P _34534) = (term356 _86925 _34533 P _34534).
Proof. exact (@lem3328400 (@I (_86925 -> Prop) _34533 _34534) (@I (_86925 -> Prop) P _34534)). Qed.
Lemma lem3328402 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) : (term285 _86925 s _34533) = (term285 _86925 s _34533).
Proof. exact (eq_refl (term285 _86925 s _34533)). Qed.
Lemma lem3328403 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) (P : _86925 -> Prop) (_34534 : _86925) : (term320 _86925 s _34533 P _34534) = (term357 _86925 s _34533 P _34534).
Proof. exact (MK_COMB (@lem3328402 _86925 s _34533) (@lem3328401 _86925 _34533 P _34534)). Qed.
Lemma lem3328405 (a : Prop) (b : Prop) : (term354 a b) = (term355 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3328406 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) (P : _86925 -> Prop) (_34534 : _86925) : (term357 _86925 s _34533 P _34534) = (term358 _86925 s _34533 P _34534).
Proof. exact (@lem3328405 (@I ((_86925 -> Prop) -> Prop) s _34533) (term279 _86925 _34533 P _34534)). Qed.
Lemma lem3328407 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) (P : _86925 -> Prop) (_34534 : _86925) : (term320 _86925 s _34533 P _34534) = (term358 _86925 s _34533 P _34534).
Proof. exact (TRANS (@lem3328403 _86925 s _34533 P _34534) (@lem3328406 _86925 s _34533 P _34534)). Qed.
Lemma lem3328409 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3328410 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) (P : _86925 -> Prop) (_34534 : _86925) : (term358 _86925 s _34533 P _34534) = (term359 _86925 s _34533 P _34534).
Proof. exact (@lem3328409 (term281 _86925 s _34533 P _34534)). Qed.
Lemma lem3328411 {_86925 : Type'} (s : type686 _86925) (_34533 : _86925 -> Prop) (P : _86925 -> Prop) (_34534 : _86925) : (term320 _86925 s _34533 P _34534) = (term359 _86925 s _34533 P _34534).
Proof. exact (TRANS (@lem3328407 _86925 s _34533 P _34534) (@lem3328410 _86925 s _34533 P _34534)). Qed.
Lemma lem3328413 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term279 _86925 t P x.
Proof. exact (conj (@lem3328391 _86925 t x s P h1) (@lem3328398 _86925 t x s P h1)). Qed.
Lemma lem3328414 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term281 _86925 s t P x.
Proof. exact (conj (@lem3328384 _86925 t x s P h1) (@lem3328413 _86925 t x s P h1)). Qed.
Lemma lem3328416 {_86925 : Type'} (_34533 : _86925 -> Prop) (_34534 : _86925) (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term359 _86925 s _34533 P _34534.
Proof. exact (EQ_MP (@lem3328411 _86925 s _34533 P _34534) (@lem3328353 _86925 _34533 _34534 t x s P h1)). Qed.
Lemma lem3328417 {_86925 : Type'} (_34533 : _86925 -> Prop) (_34534 : _86925) (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term359 _86925 s _34533 P _34534.
Proof. exact (@lem3328416 _86925 _34533 _34534 t x s P h1). Qed.
Lemma lem3328418 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term359 _86925 s t P x.
Proof. exact (@lem3328417 _86925 t x t x s P h1). Qed.
Lemma lem3328421 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : False.
Proof. exact (@lem3328418 _86925 t x s P h1 (@lem3328414 _86925 t x s P h1)). Qed.
Lemma lem3328422 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : term360.
Proof. exact (fun h0 : ~ False => @lem3328421 _86925 t x s P h1). Qed.
Lemma lem3328424 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328425 : term360 = False.
Proof. exact (@lem3328424 False). Qed.
Lemma lem3328426 {_86925 : Type'} (t : _86925 -> Prop) (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term307 _86925 t x s P) : False.
Proof. exact (EQ_MP (@lem3328425) (@lem3328422 _86925 t x s P h1)). Qed.
Lemma lem3328428 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : @I ((_86925 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3328210 _86925 s t P x' h1)). Qed.
Lemma lem3328429 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term351 _86925 s t.
Proof. exact (fun h0 : term284 _86925 s t => @lem3328428 _86925 s t P x' h1). Qed.
Lemma lem3328431 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328432 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) : (term351 _86925 s t) = (@I ((_86925 -> Prop) -> Prop) s t).
Proof. exact (@lem3328431 (@I ((_86925 -> Prop) -> Prop) s t)). Qed.
Lemma lem3328433 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : @I ((_86925 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3328432 _86925 s t) (@lem3328429 _86925 s t P x' h1)). Qed.
Lemma lem3328435 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : @I (_86925 -> Prop) t x'.
Proof. exact (proj1 (@lem3328212 _86925 s t P x' h1)). Qed.
Lemma lem3328436 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term353 _86925 t x'.
Proof. exact (fun h0 : term282 _86925 t x' => @lem3328435 _86925 s t P x' h1). Qed.
Lemma lem3328438 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328439 {_86925 : Type'} (t : _86925 -> Prop) (x' : _86925) : (term353 _86925 t x') = (@I (_86925 -> Prop) t x').
Proof. exact (@lem3328438 (@I (_86925 -> Prop) t x')). Qed.
Lemma lem3328440 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : @I (_86925 -> Prop) t x'.
Proof. exact (EQ_MP (@lem3328439 _86925 t x') (@lem3328436 _86925 s t P x' h1)). Qed.
Lemma lem3328442 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : @I (_86925 -> Prop) P x'.
Proof. exact (proj2 (@lem3328212 _86925 s t P x' h1)). Qed.
Lemma lem3328443 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term353 _86925 P x'.
Proof. exact (fun h0 : term282 _86925 P x' => @lem3328442 _86925 s t P x' h1). Qed.
Lemma lem3328445 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328446 {_86925 : Type'} (P : _86925 -> Prop) (x' : _86925) : (term353 _86925 P x') = (@I (_86925 -> Prop) P x').
Proof. exact (@lem3328445 (@I (_86925 -> Prop) P x')). Qed.
Lemma lem3328447 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : @I (_86925 -> Prop) P x'.
Proof. exact (EQ_MP (@lem3328446 _86925 P x') (@lem3328443 _86925 s t P x' h1)). Qed.
Lemma lem3328449 (a : Prop) (b : Prop) : (term354 a b) = (term355 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3328450 {_86925 : Type'} (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term297 _86925 _34536 P _34535) = (term356 _86925 _34536 P _34535).
Proof. exact (@lem3328449 (@I (_86925 -> Prop) _34536 _34535) (@I (_86925 -> Prop) P _34535)). Qed.
Lemma lem3328451 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) : (term285 _86925 s _34536) = (term285 _86925 s _34536).
Proof. exact (eq_refl (term285 _86925 s _34536)). Qed.
Lemma lem3328452 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term320 _86925 s _34536 P _34535) = (term357 _86925 s _34536 P _34535).
Proof. exact (MK_COMB (@lem3328451 _86925 s _34536) (@lem3328450 _86925 _34536 P _34535)). Qed.
Lemma lem3328454 (a : Prop) (b : Prop) : (term354 a b) = (term355 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3328455 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term357 _86925 s _34536 P _34535) = (term358 _86925 s _34536 P _34535).
Proof. exact (@lem3328454 (@I ((_86925 -> Prop) -> Prop) s _34536) (term279 _86925 _34536 P _34535)). Qed.
Lemma lem3328456 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term320 _86925 s _34536 P _34535) = (term358 _86925 s _34536 P _34535).
Proof. exact (TRANS (@lem3328452 _86925 s _34536 P _34535) (@lem3328455 _86925 s _34536 P _34535)). Qed.
Lemma lem3328458 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3328459 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term358 _86925 s _34536 P _34535) = (term359 _86925 s _34536 P _34535).
Proof. exact (@lem3328458 (term281 _86925 s _34536 P _34535)). Qed.
Lemma lem3328460 {_86925 : Type'} (s : type686 _86925) (_34536 : _86925 -> Prop) (P : _86925 -> Prop) (_34535 : _86925) : (term320 _86925 s _34536 P _34535) = (term359 _86925 s _34536 P _34535).
Proof. exact (TRANS (@lem3328456 _86925 s _34536 P _34535) (@lem3328459 _86925 s _34536 P _34535)). Qed.
Lemma lem3328462 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term279 _86925 t P x'.
Proof. exact (conj (@lem3328440 _86925 s t P x' h1) (@lem3328447 _86925 s t P x' h1)). Qed.
Lemma lem3328463 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term281 _86925 s t P x'.
Proof. exact (conj (@lem3328433 _86925 s t P x' h1) (@lem3328462 _86925 s t P x' h1)). Qed.
Lemma lem3328465 {_86925 : Type'} (_34536 : _86925 -> Prop) (_34535 : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term359 _86925 s _34536 P _34535.
Proof. exact (EQ_MP (@lem3328460 _86925 s _34536 P _34535) (@lem3328371 _86925 _34536 _34535 s t P x' h1)). Qed.
Lemma lem3328466 {_86925 : Type'} (_34536 : _86925 -> Prop) (_34535 : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term359 _86925 s _34536 P _34535.
Proof. exact (@lem3328465 _86925 _34536 _34535 s t P x' h1). Qed.
Lemma lem3328467 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term359 _86925 s t P x'.
Proof. exact (@lem3328466 _86925 t x' s t P x' h1). Qed.
Lemma lem3328470 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : False.
Proof. exact (@lem3328467 _86925 s t P x' h1 (@lem3328463 _86925 s t P x' h1)). Qed.
Lemma lem3328471 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : term360.
Proof. exact (fun h0 : ~ False => @lem3328470 _86925 s t P x' h1). Qed.
Lemma lem3328473 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3328474 : term360 = False.
Proof. exact (@lem3328473 False). Qed.
Lemma lem3328475 {_86925 : Type'} (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term294 _86925 s t P x') : False.
Proof. exact (EQ_MP (@lem3328474) (@lem3328471 _86925 s t P x' h1)). Qed.
Lemma lem3328476 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (x' : _86925) (h1 : term270 _86925 x s t P x') : False.
Proof. exact (or_elim (@lem3328201 _86925 x s t P x' h1) (fun h0 : term307 _86925 t x s P => @lem3328426 _86925 t x s P h0) (fun h0 : term294 _86925 s t P x' => @lem3328475 _86925 s t P x' h0)). Qed.
Lemma lem3328477 {_86925 : Type'} (x : _86925) (s : type686 _86925) (t : _86925 -> Prop) (P : _86925 -> Prop) (h1 : term273 _86925 x s t P) : False.
Proof. exact (ex_elim (@lem3328046 _86925 x s t P h1) (fun x' : _86925 => fun h0 : term272 _86925 x s t P x' => @lem3328476 _86925 x s t P x' h0)). Qed.
Lemma lem3328478 {_86925 : Type'} (x : _86925) (s : type686 _86925) (P : _86925 -> Prop) (h1 : term275 _86925 x s P) : False.
Proof. exact (ex_elim (@lem3328045 _86925 x s P h1) (fun t : _86925 -> Prop => fun h0 : term274 _86925 x s P t => @lem3328477 _86925 x s t P h0)). Qed.
Lemma lem3328479 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (h1 : term77 _86925 s P) : False.
Proof. exact (ex_elim (@lem3328044 _86925 s P h1) (fun x : _86925 => fun h0 : term276 _86925 s P x => @lem3328478 _86925 x s P h0)). Qed.
Lemma lem3328480 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (h1 : term77 _86925 s P) : (term77 _86925 s P) = False.
Proof. exact (prop_ext (fun h2 : term77 _86925 s P => @lem3328479 _86925 s P h1) (fun h2 : False => @lem3327402 _86925 s P h1)). Qed.
Lemma lem3328481 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) (h1 : term77 _86925 s P) : False.
Proof. exact (EQ_MP (@lem3328480 _86925 s P h1) (@lem3327402 _86925 s P h1)). Qed.
Lemma lem3328482 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : term76 _86925 s P.
Proof. exact (fun h0 : term77 _86925 s P => @lem3328481 _86925 s P h0). Qed.
Lemma lem3328483 {_86925 : Type'} (s : type686 _86925) (P : _86925 -> Prop) : (term23 _86925 s P) = (term71 _86925 s P).
Proof. exact (EQ_MP (@lem3327401 _86925 s P) (@lem3328482 _86925 s P)). Qed.
Lemma lem3328488 {_86925 : Type'} (P : _86925 -> Prop) : term73 _86925 P.
Proof. exact (fun s : type686 _86925 => @lem3328483 _86925 s P). Qed.
Lemma lem3328493 {_86925 : Type'} : term75 _86925.
Proof. exact (fun P : _86925 -> Prop => @lem3328488 _86925 P). Qed.
Lemma lem3328494 {_86925 : Type'} : term49 _86925.
Proof. exact (EQ_MP (@lem3327397 _86925) (@lem3328493 _86925)). Qed.
Lemma lem3328496 {_86925 : Type'} : term49 _86925.
Proof. exact (@lem3327139 _86925 (@lem3328494 _86925)). Qed.
Lemma lem3328497 {_86925 : Type'} (h1 : term50 _86925) : False.
Proof. exact (@lem3328496 _86925 (@lem3327123 _86925 h1)). Qed.
Lemma lem3328498 {_86925 : Type'} (h1 : term50 _86925) : (term50 _86925) = False.
Proof. exact (prop_ext (fun h2 : term50 _86925 => @lem3328497 _86925 h1) (fun h2 : False => @lem3327123 _86925 h1)). Qed.
Lemma lem3328499 {_86925 : Type'} (h1 : term50 _86925) : False.
Proof. exact (EQ_MP (@lem3328498 _86925 h1) (@lem3327123 _86925 h1)). Qed.
Lemma lem3328500 {_86925 : Type'} : term49 _86925.
Proof. exact (fun h0 : term50 _86925 => @lem3328499 _86925 h0). Qed.
Lemma lem3328501 {_86925 : Type'} : term47 _86925.
Proof. exact (EQ_MP (@lem3327122 _86925) (@lem3328500 _86925)). Qed.
Lemma lem3328503 {_86925 : Type'} : term46 _86925.
Proof. exact (EQ_MP (@lem3327118 _86925) (@lem3328501 _86925)). Qed.
