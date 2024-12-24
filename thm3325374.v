Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3325374_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Lemma lem3324025 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3324026 {_86841 : Type'} (s : type686 _86841) (x : _86841) : (term0 _86841 x s) = (term1 _86841 s x).
Proof. exact (@lem3324025 _86841 s x). Qed.
Lemma lem3324027 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term2 _86841 x s u) = (term3 _86841 s u x).
Proof. exact (@lem3324026 _86841 (@INSERT (_86841 -> Prop) s u) x). Qed.
Lemma lem3324035 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A x y s) = (term5 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3324036 {_86841 : Type'} (y : _86841 -> Prop) (x : _86841 -> Prop) (s : type686 _86841) : (term6 _86841 x y s) = (term7 _86841 y x s).
Proof. exact (@lem3324035 (_86841 -> Prop) y x s). Qed.
Lemma lem3324037 {_86841 : Type'} (s : _86841 -> Prop) (t : _86841 -> Prop) (u : type686 _86841) : (term6 _86841 t s u) = (term7 _86841 s t u).
Proof. exact (@lem3324036 _86841 s t u). Qed.
Lemma lem3324043 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3324044 {_86841 : Type'} (P : type686 _86841) (x : _86841 -> Prop) : (@IN (_86841 -> Prop) x P) = (P x).
Proof. exact (@lem3324043 (_86841 -> Prop) P x). Qed.
Lemma lem3324045 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (@IN (_86841 -> Prop) t u) = (u t).
Proof. exact (@lem3324044 _86841 u t). Qed.
Lemma lem3324046 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) : (term8 _86841 t s) = (term8 _86841 t s).
Proof. exact (eq_refl (term8 _86841 t s)). Qed.
Lemma lem3324047 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term7 _86841 s t u) = (term9 _86841 s u t).
Proof. exact (MK_COMB (@lem3324046 _86841 t s) (@lem3324045 _86841 u t)). Qed.
Lemma lem3324050 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term6 _86841 t s u) = (term9 _86841 s u t).
Proof. exact (TRANS (@lem3324037 _86841 s t u) (@lem3324047 _86841 s u t)). Qed.
Lemma lem3324051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324052 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term10 _86841 t s u) = (term11 _86841 s u t).
Proof. exact (MK_COMB (@lem3324051) (@lem3324050 _86841 s u t)). Qed.
Lemma lem3324054 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3324055 {_86841 : Type'} (P : _86841 -> Prop) (x : _86841) : (@IN _86841 x P) = (P x).
Proof. exact (@lem3324054 _86841 P x). Qed.
Lemma lem3324056 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (@IN _86841 x t) = (t x).
Proof. exact (@lem3324055 _86841 t x). Qed.
Lemma lem3324057 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term12 _86841 s u x t) = (term13 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324052 _86841 s u t) (@lem3324056 _86841 t x)). Qed.
Lemma lem3324060 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term14 _86841 s u x) = (term15 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324057 _86841 s u t x)). Qed.
Lemma lem3324061 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324062 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term3 _86841 s u x) = (term16 _86841 s u x).
Proof. exact (MK_COMB (@lem3324061 _86841) (@lem3324060 _86841 s u x)). Qed.
Lemma lem3324067 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term2 _86841 x s u) = (term16 _86841 s u x).
Proof. exact (TRANS (@lem3324027 _86841 s u x) (@lem3324062 _86841 s u x)). Qed.
Lemma lem3324068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3324069 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term17 _86841 x s u) = (term18 _86841 s u x).
Proof. exact (MK_COMB (@lem3324068) (@lem3324067 _86841 s u x)). Qed.
Lemma lem3324071 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term19 A x s t) = (term20 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3324072 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (t : _86841 -> Prop) : (term19 _86841 x s t) = (term20 _86841 s x t).
Proof. exact (@lem3324071 _86841 s x t). Qed.
Lemma lem3324073 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) : (term21 _86841 x s u) = (term22 _86841 s x u).
Proof. exact (@lem3324072 _86841 s x (@UNIONS _86841 u)). Qed.
Lemma lem3324077 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3324078 {_86841 : Type'} (P : _86841 -> Prop) (x : _86841) : (@IN _86841 x P) = (P x).
Proof. exact (@lem3324077 _86841 P x). Qed.
Lemma lem3324079 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (@IN _86841 x s) = (s x).
Proof. exact (@lem3324078 _86841 s x). Qed.
Lemma lem3324080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324081 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term23 _86841 x s) = (term24 _86841 s x).
Proof. exact (MK_COMB (@lem3324080) (@lem3324079 _86841 s x)). Qed.
Lemma lem3324083 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3324084 {_86841 : Type'} (s : type686 _86841) (x : _86841) : (term0 _86841 x s) = (term1 _86841 s x).
Proof. exact (@lem3324083 _86841 s x). Qed.
Lemma lem3324085 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term0 _86841 x u) = (term1 _86841 u x).
Proof. exact (@lem3324084 _86841 u x). Qed.
Lemma lem3324093 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3324094 {_86841 : Type'} (P : type686 _86841) (x : _86841 -> Prop) : (@IN (_86841 -> Prop) x P) = (P x).
Proof. exact (@lem3324093 (_86841 -> Prop) P x). Qed.
Lemma lem3324095 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (@IN (_86841 -> Prop) t u) = (u t).
Proof. exact (@lem3324094 _86841 u t). Qed.
Lemma lem3324096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324097 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (term25 _86841 t u) = (term26 _86841 u t).
Proof. exact (MK_COMB (@lem3324096) (@lem3324095 _86841 u t)). Qed.
Lemma lem3324099 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3324100 {_86841 : Type'} (P : _86841 -> Prop) (x : _86841) : (@IN _86841 x P) = (P x).
Proof. exact (@lem3324099 _86841 P x). Qed.
Lemma lem3324101 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (@IN _86841 x t) = (t x).
Proof. exact (@lem3324100 _86841 t x). Qed.
Lemma lem3324102 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term27 _86841 u x t) = (term28 _86841 u t x).
Proof. exact (MK_COMB (@lem3324097 _86841 u t) (@lem3324101 _86841 t x)). Qed.
Lemma lem3324105 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term29 _86841 u x) = (term30 _86841 u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324102 _86841 u t x)). Qed.
Lemma lem3324106 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324107 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term1 _86841 u x) = (term31 _86841 u x).
Proof. exact (MK_COMB (@lem3324106 _86841) (@lem3324105 _86841 u x)). Qed.
Lemma lem3324112 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term0 _86841 x u) = (term31 _86841 u x).
Proof. exact (TRANS (@lem3324085 _86841 u x) (@lem3324107 _86841 u x)). Qed.
Lemma lem3324113 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term22 _86841 s x u) = (term32 _86841 s u x).
Proof. exact (MK_COMB (@lem3324081 _86841 s x) (@lem3324112 _86841 u x)). Qed.
Lemma lem3324116 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term21 _86841 x s u) = (term32 _86841 s u x).
Proof. exact (TRANS (@lem3324073 _86841 s x u) (@lem3324113 _86841 s u x)). Qed.
Lemma lem3324117 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : ((term2 _86841 x s u) = (term21 _86841 x s u)) = ((term16 _86841 s u x) = (term32 _86841 s u x)).
Proof. exact (MK_COMB (@lem3324069 _86841 s u x) (@lem3324116 _86841 s u x)). Qed.
Lemma lem3324120 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term33 _86841 s u) = (term34 _86841 s u).
Proof. exact (fun_ext (fun x : _86841 => @lem3324117 _86841 s u x)). Qed.
Lemma lem3324121 {_86841 : Type'} : (@all _86841) = (@all _86841).
Proof. exact (eq_refl (@all _86841)). Qed.
Lemma lem3324122 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term35 _86841 s u) = (term36 _86841 s u).
Proof. exact (MK_COMB (@lem3324121 _86841) (@lem3324120 _86841 s u)). Qed.
Lemma lem3324127 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term36 _86841 s u) = (term35 _86841 s u).
Proof. exact (SYM (@lem3324122 _86841 s u)). Qed.
Lemma lem3324129 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3324130 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term36 _86841 s u) = (term38 _86841 s u).
Proof. exact (@lem3324129 (term36 _86841 s u)). Qed.
Lemma lem3324131 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term38 _86841 s u) = (term36 _86841 s u).
Proof. exact (SYM (@lem3324130 _86841 s u)). Qed.
Lemma lem3324132 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term39 _86841 s u) : term39 _86841 s u.
Proof. exact (h1). Qed.
Lemma lem3324135 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term38 _86841 s u) : term38 _86841 s u.
Proof. exact (h1). Qed.
Lemma lem3324136 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term40 _86841 s u.
Proof. exact (fun h0 : term38 _86841 s u => @lem3324135 _86841 s u h0). Qed.
Lemma lem3324137 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term40 _86841 s u) : term40 _86841 s u.
Proof. exact (h1). Qed.
Lemma lem3324138 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term38 _86841 s u) : term38 _86841 s u.
Proof. exact (h1). Qed.
Lemma lem3324139 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term38 _86841 s u) (h2 : term40 _86841 s u) : term38 _86841 s u.
Proof. exact (@lem3324137 _86841 s u h2 (@lem3324138 _86841 s u h1)). Qed.
Lemma lem3324140 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term38 _86841 s u) : term41 _86841 s u.
Proof. exact (fun h0 : term40 _86841 s u => @lem3324139 _86841 s u h1 h0). Qed.
Lemma lem3324141 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term40 _86841 s u) : term40 _86841 s u.
Proof. exact (h1). Qed.
Lemma lem3324142 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term38 _86841 s u) (h2 : term40 _86841 s u) : term38 _86841 s u.
Proof. exact (@lem3324140 _86841 s u h1 (@lem3324141 _86841 s u h2)). Qed.
Lemma lem3324143 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term40 _86841 s u) : term40 _86841 s u.
Proof. exact (fun h0 : term38 _86841 s u => @lem3324142 _86841 s u h0 h1). Qed.
Lemma lem3324144 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term42 _86841 s u.
Proof. exact (fun h0 : term40 _86841 s u => @lem3324143 _86841 s u h0). Qed.
Lemma lem3324147 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term40 _86841 s u.
Proof. exact (@lem3324144 _86841 s u (@lem3324136 _86841 s u)). Qed.
Lemma lem3324148 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term40 _86841 s u.
Proof. exact (@lem3324147 _86841 s u). Qed.
Lemma lem3324158 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3324159 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term38 _86841 s u) = (term43 _86841 s u).
Proof. exact (@lem3324158 (term39 _86841 s u)). Qed.
Lemma lem3324161 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3324162 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term43 _86841 s u) = (term36 _86841 s u).
Proof. exact (@lem3324161 (term36 _86841 s u)). Qed.
Lemma lem3324167 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term38 _86841 s u) = (term36 _86841 s u).
Proof. exact (TRANS (@lem3324159 _86841 s u) (@lem3324162 _86841 s u)). Qed.
Lemma lem3324252 {_86841 : Type'} (u : type686 _86841) : (term45 _86841 u) = (term46 _86841 u).
Proof. exact (fun_ext (fun s : _86841 -> Prop => @lem3324167 _86841 s u)). Qed.
Lemma lem3324253 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324254 {_86841 : Type'} (u : type686 _86841) : (term47 _86841 u) = (term48 _86841 u).
Proof. exact (MK_COMB (@lem3324253 _86841) (@lem3324252 _86841 u)). Qed.
Lemma lem3324259 {_86841 : Type'} : (term49 _86841) = (term50 _86841).
Proof. exact (fun_ext (fun u : type686 _86841 => @lem3324254 _86841 u)). Qed.
Lemma lem3324260 {_86841 : Type'} : (@all ((_86841 -> Prop) -> Prop)) = (@all ((_86841 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86841 -> Prop) -> Prop))). Qed.
Lemma lem3324269 {_86841 : Type'} : (term51 _86841) = (term52 _86841).
Proof. exact (MK_COMB (@lem3324260 _86841) (@lem3324259 _86841)). Qed.
Lemma lem3324274 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term28 _86841 u t x) = (term28 _86841 u t x).
Proof. exact (eq_refl (term28 _86841 u t x)). Qed.
Lemma lem3324275 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term30 _86841 u x) = (term30 _86841 u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324274 _86841 u t x)). Qed.
Lemma lem3324276 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324277 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term31 _86841 u x) = (term31 _86841 u x).
Proof. exact (MK_COMB (@lem3324276 _86841) (@lem3324275 _86841 u x)). Qed.
Lemma lem3324280 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term24 _86841 s x) = (term24 _86841 s x).
Proof. exact (eq_refl (term24 _86841 s x)). Qed.
Lemma lem3324281 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term32 _86841 s u x) = (term32 _86841 s u x).
Proof. exact (MK_COMB (@lem3324280 _86841 s x) (@lem3324277 _86841 u x)). Qed.
Lemma lem3324290 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term13 _86841 s u t x) = (term13 _86841 s u t x).
Proof. exact (eq_refl (term13 _86841 s u t x)). Qed.
Lemma lem3324291 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term15 _86841 s u x) = (term15 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324290 _86841 s u t x)). Qed.
Lemma lem3324292 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324293 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term16 _86841 s u x) = (term16 _86841 s u x).
Proof. exact (MK_COMB (@lem3324292 _86841) (@lem3324291 _86841 s u x)). Qed.
Lemma lem3324294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3324295 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term18 _86841 s u x) = (term18 _86841 s u x).
Proof. exact (MK_COMB (@lem3324294) (@lem3324293 _86841 s u x)). Qed.
Lemma lem3324296 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : ((term16 _86841 s u x) = (term32 _86841 s u x)) = ((term16 _86841 s u x) = (term32 _86841 s u x)).
Proof. exact (MK_COMB (@lem3324295 _86841 s u x) (@lem3324281 _86841 s u x)). Qed.
Lemma lem3324297 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term34 _86841 s u) = (term34 _86841 s u).
Proof. exact (fun_ext (fun x : _86841 => @lem3324296 _86841 s u x)). Qed.
Lemma lem3324298 {_86841 : Type'} : (@all _86841) = (@all _86841).
Proof. exact (eq_refl (@all _86841)). Qed.
Lemma lem3324299 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term36 _86841 s u) = (term36 _86841 s u).
Proof. exact (MK_COMB (@lem3324298 _86841) (@lem3324297 _86841 s u)). Qed.
Lemma lem3324300 {_86841 : Type'} (u : type686 _86841) : (term46 _86841 u) = (term46 _86841 u).
Proof. exact (fun_ext (fun s : _86841 -> Prop => @lem3324299 _86841 s u)). Qed.
Lemma lem3324301 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324302 {_86841 : Type'} (u : type686 _86841) : (term48 _86841 u) = (term48 _86841 u).
Proof. exact (MK_COMB (@lem3324301 _86841) (@lem3324300 _86841 u)). Qed.
Lemma lem3324303 {_86841 : Type'} : (term50 _86841) = (term50 _86841).
Proof. exact (fun_ext (fun u : type686 _86841 => @lem3324302 _86841 u)). Qed.
Lemma lem3324304 {_86841 : Type'} : (@all ((_86841 -> Prop) -> Prop)) = (@all ((_86841 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_86841 -> Prop) -> Prop))). Qed.
Lemma lem3324305 {_86841 : Type'} : (term52 _86841) = (term52 _86841).
Proof. exact (MK_COMB (@lem3324304 _86841) (@lem3324303 _86841)). Qed.
Lemma lem3324346 {_86841 : Type'} : (term51 _86841) = (term52 _86841).
Proof. exact (TRANS (@lem3324269 _86841) (@lem3324305 _86841)). Qed.
Lemma lem3324347 {_86841 : Type'} : (term52 _86841) = (term51 _86841).
Proof. exact (SYM (@lem3324346 _86841)). Qed.
Lemma lem3324349 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3324350 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : ((term16 _86841 s u x) = (term32 _86841 s u x)) = (term53 _86841 s u x).
Proof. exact (@lem3324349 ((term16 _86841 s u x) = (term32 _86841 s u x))). Qed.
Lemma lem3324351 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term53 _86841 s u x) = ((term16 _86841 s u x) = (term32 _86841 s u x)).
Proof. exact (SYM (@lem3324350 _86841 s u x)). Qed.
Lemma lem3324352 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term54 _86841 s u x) : term54 _86841 s u x.
Proof. exact (h1). Qed.
Lemma lem3324361 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term55 _86841 s u t) = (term56 _86841 s u t).
Proof. exact (@lem17160 (t = s) (u t)). Qed.
Lemma lem3324365 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (term57 _86841 t x) = (term57 _86841 t x).
Proof. exact (eq_refl (term57 _86841 t x)). Qed.
Lemma lem3324367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324368 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term58 _86841 s u t) = (term59 _86841 s u t).
Proof. exact (MK_COMB (@lem3324367) (@lem3324361 _86841 s u t)). Qed.
Lemma lem3324369 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term60 _86841 s u t x) = (term61 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324368 _86841 s u t) (@lem3324365 _86841 t x)). Qed.
Lemma lem3324370 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term62 _86841 s u t x) = (term60 _86841 s u t x).
Proof. exact (@lem17045 (term9 _86841 s u t) (t x)). Qed.
Lemma lem3324371 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term62 _86841 s u t x) = (term61 _86841 s u t x).
Proof. exact (TRANS (@lem3324370 _86841 s u t x) (@lem3324369 _86841 s u t x)). Qed.
Lemma lem3324374 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term13 _86841 s u t x) = (term13 _86841 s u t x).
Proof. exact (eq_refl (term13 _86841 s u t x)). Qed.
Lemma lem3324375 {_86841 : Type'} (P : type686 _86841) : (term63 _86841 P) = (term64 _86841 P).
Proof. exact (@lem18394 (_86841 -> Prop) P). Qed.
Lemma lem3324376 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term65 _86841 s u x) = (term66 _86841 s u x).
Proof. exact (@lem3324375 _86841 (term15 _86841 s u x)). Qed.
Lemma lem3324377 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term67 _86841 s u x t) = (term13 _86841 s u t x).
Proof. exact (eq_refl (term67 _86841 s u x t)). Qed.
Lemma lem3324378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3324379 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term68 _86841 s u x t) = (term62 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324378) (@lem3324377 _86841 s u t x)). Qed.
Lemma lem3324380 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term68 _86841 s u x t) = (term61 _86841 s u t x).
Proof. exact (TRANS (@lem3324379 _86841 s u t x) (@lem3324371 _86841 s u t x)). Qed.
Lemma lem3324381 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term69 _86841 s u x) = (term70 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324380 _86841 s u t x)). Qed.
Lemma lem3324382 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324383 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term66 _86841 s u x) = (term71 _86841 s u x).
Proof. exact (MK_COMB (@lem3324382 _86841) (@lem3324381 _86841 s u x)). Qed.
Lemma lem3324384 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term65 _86841 s u x) = (term71 _86841 s u x).
Proof. exact (TRANS (@lem3324376 _86841 s u x) (@lem3324383 _86841 s u x)). Qed.
Lemma lem3324385 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term15 _86841 s u x) = (term15 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324374 _86841 s u t x)). Qed.
Lemma lem3324386 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324387 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term16 _86841 s u x) = (term16 _86841 s u x).
Proof. exact (MK_COMB (@lem3324386 _86841) (@lem3324385 _86841 s u x)). Qed.
Lemma lem3324398 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term72 _86841 u t x) = (term73 _86841 u t x).
Proof. exact (@lem17045 (u t) (t x)). Qed.
Lemma lem3324401 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term28 _86841 u t x) = (term28 _86841 u t x).
Proof. exact (eq_refl (term28 _86841 u t x)). Qed.
Lemma lem3324402 {_86841 : Type'} (P : type686 _86841) : (term63 _86841 P) = (term64 _86841 P).
Proof. exact (@lem18394 (_86841 -> Prop) P). Qed.
Lemma lem3324403 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term74 _86841 u x) = (term75 _86841 u x).
Proof. exact (@lem3324402 _86841 (term30 _86841 u x)). Qed.
Lemma lem3324404 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term76 _86841 u x t) = (term28 _86841 u t x).
Proof. exact (eq_refl (term76 _86841 u x t)). Qed.
Lemma lem3324405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3324406 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term77 _86841 u x t) = (term72 _86841 u t x).
Proof. exact (MK_COMB (@lem3324405) (@lem3324404 _86841 u t x)). Qed.
Lemma lem3324407 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term77 _86841 u x t) = (term73 _86841 u t x).
Proof. exact (TRANS (@lem3324406 _86841 u t x) (@lem3324398 _86841 u t x)). Qed.
Lemma lem3324408 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term78 _86841 u x) = (term79 _86841 u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324407 _86841 u t x)). Qed.
Lemma lem3324409 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324410 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term75 _86841 u x) = (term80 _86841 u x).
Proof. exact (MK_COMB (@lem3324409 _86841) (@lem3324408 _86841 u x)). Qed.
Lemma lem3324411 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term74 _86841 u x) = (term80 _86841 u x).
Proof. exact (TRANS (@lem3324403 _86841 u x) (@lem3324410 _86841 u x)). Qed.
Lemma lem3324412 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term30 _86841 u x) = (term30 _86841 u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324401 _86841 u t x)). Qed.
Lemma lem3324413 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324414 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term31 _86841 u x) = (term31 _86841 u x).
Proof. exact (MK_COMB (@lem3324413 _86841) (@lem3324412 _86841 u x)). Qed.
Lemma lem3324416 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term81 _86841 s x) = (term81 _86841 s x).
Proof. exact (eq_refl (term81 _86841 s x)). Qed.
Lemma lem3324417 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term82 _86841 s u x) = (term83 _86841 s u x).
Proof. exact (MK_COMB (@lem3324416 _86841 s x) (@lem3324411 _86841 u x)). Qed.
Lemma lem3324418 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term84 _86841 s u x) = (term82 _86841 s u x).
Proof. exact (@lem17160 (s x) (term31 _86841 u x)). Qed.
Lemma lem3324419 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term84 _86841 s u x) = (term83 _86841 s u x).
Proof. exact (TRANS (@lem3324418 _86841 s u x) (@lem3324417 _86841 s u x)). Qed.
Lemma lem3324421 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term24 _86841 s x) = (term24 _86841 s x).
Proof. exact (eq_refl (term24 _86841 s x)). Qed.
Lemma lem3324422 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term32 _86841 s u x) = (term32 _86841 s u x).
Proof. exact (MK_COMB (@lem3324421 _86841 s x) (@lem3324414 _86841 u x)). Qed.
Lemma lem3324423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324424 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term85 _86841 s u x) = (term86 _86841 s u x).
Proof. exact (MK_COMB (@lem3324423) (@lem3324384 _86841 s u x)). Qed.
Lemma lem3324425 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term87 _86841 s u x) = (term88 _86841 s u x).
Proof. exact (MK_COMB (@lem3324424 _86841 s u x) (@lem3324422 _86841 s u x)). Qed.
Lemma lem3324426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324427 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term89 _86841 s u x) = (term89 _86841 s u x).
Proof. exact (MK_COMB (@lem3324426) (@lem3324387 _86841 s u x)). Qed.
Lemma lem3324428 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term90 _86841 s u x) = (term91 _86841 s u x).
Proof. exact (MK_COMB (@lem3324427 _86841 s u x) (@lem3324419 _86841 s u x)). Qed.
Lemma lem3324429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324430 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term92 _86841 s u x) = (term93 _86841 s u x).
Proof. exact (MK_COMB (@lem3324429) (@lem3324428 _86841 s u x)). Qed.
Lemma lem3324431 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term94 _86841 s u x) = (term95 _86841 s u x).
Proof. exact (MK_COMB (@lem3324430 _86841 s u x) (@lem3324425 _86841 s u x)). Qed.
Lemma lem3324432 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term54 _86841 s u x) = (term94 _86841 s u x).
Proof. exact (@lem17646 (term16 _86841 s u x) (term32 _86841 s u x)). Qed.
Lemma lem3324433 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term54 _86841 s u x) = (term95 _86841 s u x).
Proof. exact (TRANS (@lem3324432 _86841 s u x) (@lem3324431 _86841 s u x)). Qed.
Lemma lem3324608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3324609 {_86841 : Type'} (P : type686 _86841) (Q : Prop) : (term98 _86841 P Q) = (term99 _86841 P Q).
Proof. exact (@lem3324608 (_86841 -> Prop) P Q). Qed.
Lemma lem3324610 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term100 _86841 s u x) = (term101 _86841 s u x).
Proof. exact (@lem3324609 _86841 (term15 _86841 s u x) (term83 _86841 s u x)). Qed.
Lemma lem3324611 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term67 _86841 s u x t) = (term13 _86841 s u t x).
Proof. exact (eq_refl (term67 _86841 s u x t)). Qed.
Lemma lem3324612 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term102 _86841 s u x) = (term15 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324611 _86841 s u t x)). Qed.
Lemma lem3324613 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324614 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term103 _86841 s u x) = (term16 _86841 s u x).
Proof. exact (MK_COMB (@lem3324613 _86841) (@lem3324612 _86841 s u x)). Qed.
Lemma lem3324615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324616 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term104 _86841 s u x) = (term89 _86841 s u x).
Proof. exact (MK_COMB (@lem3324615) (@lem3324614 _86841 s u x)). Qed.
Lemma lem3324617 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term83 _86841 s u x) = (term83 _86841 s u x).
Proof. exact (eq_refl (term83 _86841 s u x)). Qed.
Lemma lem3324618 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term100 _86841 s u x) = (term91 _86841 s u x).
Proof. exact (MK_COMB (@lem3324616 _86841 s u x) (@lem3324617 _86841 s u x)). Qed.
Lemma lem3324619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3324620 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term105 _86841 s u x) = (term106 _86841 s u x).
Proof. exact (MK_COMB (@lem3324619) (@lem3324618 _86841 s u x)). Qed.
Lemma lem3324621 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term67 _86841 s u x t) = (term13 _86841 s u t x).
Proof. exact (eq_refl (term67 _86841 s u x t)). Qed.
Lemma lem3324622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324623 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term107 _86841 s u x t) = (term108 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324622) (@lem3324621 _86841 s u t x)). Qed.
Lemma lem3324624 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term83 _86841 s u x) = (term83 _86841 s u x).
Proof. exact (eq_refl (term83 _86841 s u x)). Qed.
Lemma lem3324625 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term109 _86841 t s u x) = (term110 _86841 t s u x).
Proof. exact (MK_COMB (@lem3324623 _86841 s u t x) (@lem3324624 _86841 s u x)). Qed.
Lemma lem3324626 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term111 _86841 s u x) = (term112 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324625 _86841 t s u x)). Qed.
Lemma lem3324627 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324628 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term101 _86841 s u x) = (term113 _86841 s u x).
Proof. exact (MK_COMB (@lem3324627 _86841) (@lem3324626 _86841 s u x)). Qed.
Lemma lem3324629 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : ((term100 _86841 s u x) = (term101 _86841 s u x)) = ((term91 _86841 s u x) = (term113 _86841 s u x)).
Proof. exact (MK_COMB (@lem3324620 _86841 s u x) (@lem3324628 _86841 s u x)). Qed.
Lemma lem3324630 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term91 _86841 s u x) = (term113 _86841 s u x).
Proof. exact (EQ_MP (@lem3324629 _86841 s u x) (@lem3324610 _86841 s u x)). Qed.
Lemma lem3324631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324632 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term93 _86841 s u x) = (term114 _86841 s u x).
Proof. exact (MK_COMB (@lem3324631) (@lem3324630 _86841 s u x)). Qed.
Lemma lem3324634 {A : Type'} (P : Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3324635 {_86841 : Type'} (P : Prop) (Q : type686 _86841) : (term117 _86841 P Q) = (term118 _86841 P Q).
Proof. exact (@lem3324634 (_86841 -> Prop) P Q). Qed.
Lemma lem3324636 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term119 _86841 s u x) = (term120 _86841 s u x).
Proof. exact (@lem3324635 _86841 (s x) (term30 _86841 u x)). Qed.
Lemma lem3324637 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term76 _86841 u x t) = (term28 _86841 u t x).
Proof. exact (eq_refl (term76 _86841 u x t)). Qed.
Lemma lem3324638 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term121 _86841 u x) = (term30 _86841 u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324637 _86841 u t x)). Qed.
Lemma lem3324639 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324640 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term122 _86841 u x) = (term31 _86841 u x).
Proof. exact (MK_COMB (@lem3324639 _86841) (@lem3324638 _86841 u x)). Qed.
Lemma lem3324641 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term24 _86841 s x) = (term24 _86841 s x).
Proof. exact (eq_refl (term24 _86841 s x)). Qed.
Lemma lem3324642 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term119 _86841 s u x) = (term32 _86841 s u x).
Proof. exact (MK_COMB (@lem3324641 _86841 s x) (@lem3324640 _86841 u x)). Qed.
Lemma lem3324643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3324644 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term123 _86841 s u x) = (term124 _86841 s u x).
Proof. exact (MK_COMB (@lem3324643) (@lem3324642 _86841 s u x)). Qed.
Lemma lem3324645 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term76 _86841 u x t) = (term28 _86841 u t x).
Proof. exact (eq_refl (term76 _86841 u x t)). Qed.
Lemma lem3324646 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term24 _86841 s x) = (term24 _86841 s x).
Proof. exact (eq_refl (term24 _86841 s x)). Qed.
Lemma lem3324647 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term125 _86841 s u x t) = (term126 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324646 _86841 s x) (@lem3324645 _86841 u t x)). Qed.
Lemma lem3324648 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term127 _86841 s u x) = (term128 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324647 _86841 s u t x)). Qed.
Lemma lem3324649 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324650 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term120 _86841 s u x) = (term129 _86841 s u x).
Proof. exact (MK_COMB (@lem3324649 _86841) (@lem3324648 _86841 s u x)). Qed.
Lemma lem3324651 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : ((term119 _86841 s u x) = (term120 _86841 s u x)) = ((term32 _86841 s u x) = (term129 _86841 s u x)).
Proof. exact (MK_COMB (@lem3324644 _86841 s u x) (@lem3324650 _86841 s u x)). Qed.
Lemma lem3324652 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term32 _86841 s u x) = (term129 _86841 s u x).
Proof. exact (EQ_MP (@lem3324651 _86841 s u x) (@lem3324636 _86841 s u x)). Qed.
Lemma lem3324653 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term86 _86841 s u x) = (term86 _86841 s u x).
Proof. exact (eq_refl (term86 _86841 s u x)). Qed.
Lemma lem3324654 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term88 _86841 s u x) = (term130 _86841 s u x).
Proof. exact (MK_COMB (@lem3324653 _86841 s u x) (@lem3324652 _86841 s u x)). Qed.
Lemma lem3324656 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3324657 {_86841 : Type'} (P : Prop) (Q : type686 _86841) : (term133 _86841 P Q) = (term134 _86841 P Q).
Proof. exact (@lem3324656 (_86841 -> Prop) P Q). Qed.
Lemma lem3324658 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term135 _86841 s u x) = (term136 _86841 s u x).
Proof. exact (@lem3324657 _86841 (term71 _86841 s u x) (term128 _86841 s u x)). Qed.
Lemma lem3324659 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term137 _86841 s u x t) = (term126 _86841 s u t x).
Proof. exact (eq_refl (term137 _86841 s u x t)). Qed.
Lemma lem3324660 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term138 _86841 s u x) = (term128 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324659 _86841 s u t x)). Qed.
Lemma lem3324661 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324662 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term139 _86841 s u x) = (term129 _86841 s u x).
Proof. exact (MK_COMB (@lem3324661 _86841) (@lem3324660 _86841 s u x)). Qed.
Lemma lem3324663 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term86 _86841 s u x) = (term86 _86841 s u x).
Proof. exact (eq_refl (term86 _86841 s u x)). Qed.
Lemma lem3324664 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term135 _86841 s u x) = (term130 _86841 s u x).
Proof. exact (MK_COMB (@lem3324663 _86841 s u x) (@lem3324662 _86841 s u x)). Qed.
Lemma lem3324665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3324666 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term140 _86841 s u x) = (term141 _86841 s u x).
Proof. exact (MK_COMB (@lem3324665) (@lem3324664 _86841 s u x)). Qed.
Lemma lem3324667 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term137 _86841 s u x t) = (term126 _86841 s u t x).
Proof. exact (eq_refl (term137 _86841 s u x t)). Qed.
Lemma lem3324668 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term86 _86841 s u x) = (term86 _86841 s u x).
Proof. exact (eq_refl (term86 _86841 s u x)). Qed.
Lemma lem3324669 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term142 _86841 s u x t) = (term143 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324668 _86841 s u x) (@lem3324667 _86841 s u t x)). Qed.
Lemma lem3324670 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term144 _86841 s u x) = (term145 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324669 _86841 s u t x)). Qed.
Lemma lem3324671 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324672 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term136 _86841 s u x) = (term146 _86841 s u x).
Proof. exact (MK_COMB (@lem3324671 _86841) (@lem3324670 _86841 s u x)). Qed.
Lemma lem3324673 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : ((term135 _86841 s u x) = (term136 _86841 s u x)) = ((term130 _86841 s u x) = (term146 _86841 s u x)).
Proof. exact (MK_COMB (@lem3324666 _86841 s u x) (@lem3324672 _86841 s u x)). Qed.
Lemma lem3324674 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term130 _86841 s u x) = (term146 _86841 s u x).
Proof. exact (EQ_MP (@lem3324673 _86841 s u x) (@lem3324658 _86841 s u x)). Qed.
Lemma lem3324675 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term88 _86841 s u x) = (term146 _86841 s u x).
Proof. exact (TRANS (@lem3324654 _86841 s u x) (@lem3324674 _86841 s u x)). Qed.
Lemma lem3324676 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term95 _86841 s u x) = (term147 _86841 s u x).
Proof. exact (MK_COMB (@lem3324632 _86841 s u x) (@lem3324675 _86841 s u x)). Qed.
Lemma lem3324678 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3324679 {_86841 : Type'} (P : type686 _86841) (Q : type686 _86841) : (term150 _86841 P Q) = (term151 _86841 P Q).
Proof. exact (@lem3324678 (_86841 -> Prop) P Q). Qed.
Lemma lem3324680 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term152 _86841 s u x) = (term153 _86841 s u x).
Proof. exact (@lem3324679 _86841 (term112 _86841 s u x) (term145 _86841 s u x)). Qed.
Lemma lem3324681 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term154 _86841 s u x t) = (term110 _86841 t s u x).
Proof. exact (eq_refl (term154 _86841 s u x t)). Qed.
Lemma lem3324682 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term155 _86841 s u x) = (term112 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324681 _86841 t s u x)). Qed.
Lemma lem3324683 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324684 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term156 _86841 s u x) = (term113 _86841 s u x).
Proof. exact (MK_COMB (@lem3324683 _86841) (@lem3324682 _86841 s u x)). Qed.
Lemma lem3324685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324686 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term157 _86841 s u x) = (term114 _86841 s u x).
Proof. exact (MK_COMB (@lem3324685) (@lem3324684 _86841 s u x)). Qed.
Lemma lem3324687 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term158 _86841 s u x t) = (term143 _86841 s u t x).
Proof. exact (eq_refl (term158 _86841 s u x t)). Qed.
Lemma lem3324688 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term159 _86841 s u x) = (term145 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324687 _86841 s u t x)). Qed.
Lemma lem3324689 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324690 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term160 _86841 s u x) = (term146 _86841 s u x).
Proof. exact (MK_COMB (@lem3324689 _86841) (@lem3324688 _86841 s u x)). Qed.
Lemma lem3324691 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term152 _86841 s u x) = (term147 _86841 s u x).
Proof. exact (MK_COMB (@lem3324686 _86841 s u x) (@lem3324690 _86841 s u x)). Qed.
Lemma lem3324692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3324693 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term161 _86841 s u x) = (term162 _86841 s u x).
Proof. exact (MK_COMB (@lem3324692) (@lem3324691 _86841 s u x)). Qed.
Lemma lem3324694 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term154 _86841 s u x t) = (term110 _86841 t s u x).
Proof. exact (eq_refl (term154 _86841 s u x t)). Qed.
Lemma lem3324695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324696 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term163 _86841 s u x t) = (term164 _86841 t s u x).
Proof. exact (MK_COMB (@lem3324695) (@lem3324694 _86841 t s u x)). Qed.
Lemma lem3324697 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term158 _86841 s u x t) = (term143 _86841 s u t x).
Proof. exact (eq_refl (term158 _86841 s u x t)). Qed.
Lemma lem3324698 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term165 _86841 s u x t) = (term166 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324696 _86841 t s u x) (@lem3324697 _86841 s u t x)). Qed.
Lemma lem3324699 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term167 _86841 s u x) = (term168 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324698 _86841 s u t x)). Qed.
Lemma lem3324700 {_86841 : Type'} : (@ex (_86841 -> Prop)) = (@ex (_86841 -> Prop)).
Proof. exact (eq_refl (@ex (_86841 -> Prop))). Qed.
Lemma lem3324701 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term153 _86841 s u x) = (term169 _86841 s u x).
Proof. exact (MK_COMB (@lem3324700 _86841) (@lem3324699 _86841 s u x)). Qed.
Lemma lem3324702 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : ((term152 _86841 s u x) = (term153 _86841 s u x)) = ((term147 _86841 s u x) = (term169 _86841 s u x)).
Proof. exact (MK_COMB (@lem3324693 _86841 s u x) (@lem3324701 _86841 s u x)). Qed.
Lemma lem3324703 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term147 _86841 s u x) = (term169 _86841 s u x).
Proof. exact (EQ_MP (@lem3324702 _86841 s u x) (@lem3324680 _86841 s u x)). Qed.
Lemma lem3324705 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term95 _86841 s u x) = (term169 _86841 s u x).
Proof. exact (TRANS (@lem3324676 _86841 s u x) (@lem3324703 _86841 s u x)). Qed.
Lemma lem3324706 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term54 _86841 s u x) = (term169 _86841 s u x).
Proof. exact (TRANS (@lem3324433 _86841 s u x) (@lem3324705 _86841 s u x)). Qed.
Lemma lem3324707 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term54 _86841 s u x) : term169 _86841 s u x.
Proof. exact (EQ_MP (@lem3324706 _86841 s u x) (@lem3324352 _86841 s u x h1)). Qed.
Lemma lem3324708 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term166 _86841 s u t x) : term166 _86841 s u t x.
Proof. exact (h1). Qed.
Lemma lem3324713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324714 {_86841 : Type'} (f : _86841 -> Prop) (x : _86841) : (f x) = (@I (_86841 -> Prop) f x).
Proof. exact (@lem3324713 _86841 Prop f x). Qed.
Lemma lem3324716 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (t x) = (@I (_86841 -> Prop) t x).
Proof. exact (@lem3324714 _86841 t x). Qed.
Lemma lem3324721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324722 {_86841 : Type'} (f : type686 _86841) (x : _86841 -> Prop) : (f x) = (@I ((_86841 -> Prop) -> Prop) f x).
Proof. exact (@lem3324721 (_86841 -> Prop) Prop f x). Qed.
Lemma lem3324724 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (u t) = (@I ((_86841 -> Prop) -> Prop) u t).
Proof. exact (@lem3324722 _86841 u t). Qed.
Lemma lem3324725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324726 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (term26 _86841 u t) = (term170 _86841 u t).
Proof. exact (MK_COMB (@lem3324725) (@lem3324724 _86841 u t)). Qed.
Lemma lem3324727 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term28 _86841 u t x) = (term171 _86841 u t x).
Proof. exact (MK_COMB (@lem3324726 _86841 u t) (@lem3324716 _86841 t x)). Qed.
Lemma lem3324732 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324733 {_86841 : Type'} (f : _86841 -> Prop) (x : _86841) : (f x) = (@I (_86841 -> Prop) f x).
Proof. exact (@lem3324732 _86841 Prop f x). Qed.
Lemma lem3324735 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (s x) = (@I (_86841 -> Prop) s x).
Proof. exact (@lem3324733 _86841 s x). Qed.
Lemma lem3324736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324737 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term24 _86841 s x) = (term172 _86841 s x).
Proof. exact (MK_COMB (@lem3324736) (@lem3324735 _86841 s x)). Qed.
Lemma lem3324738 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term126 _86841 s u t x) = (term173 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324737 _86841 s x) (@lem3324727 _86841 u t x)). Qed.
Lemma lem3324739 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3324744 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324745 {_86841 : Type'} (f : _86841 -> Prop) (x : _86841) : (f x) = (@I (_86841 -> Prop) f x).
Proof. exact (@lem3324744 _86841 Prop f x). Qed.
Lemma lem3324747 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (t x) = (@I (_86841 -> Prop) t x).
Proof. exact (@lem3324745 _86841 t x). Qed.
Lemma lem3324748 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (term57 _86841 t x) = (term174 _86841 t x).
Proof. exact (MK_COMB (@lem3324739) (@lem3324747 _86841 t x)). Qed.
Lemma lem3324749 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3324754 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324755 {_86841 : Type'} (f : type686 _86841) (x : _86841 -> Prop) : (f x) = (@I ((_86841 -> Prop) -> Prop) f x).
Proof. exact (@lem3324754 (_86841 -> Prop) Prop f x). Qed.
Lemma lem3324757 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (u t) = (@I ((_86841 -> Prop) -> Prop) u t).
Proof. exact (@lem3324755 _86841 u t). Qed.
Lemma lem3324758 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (term175 _86841 u t) = (term176 _86841 u t).
Proof. exact (MK_COMB (@lem3324749) (@lem3324757 _86841 u t)). Qed.
Lemma lem3324767 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) : (term177 _86841 t s) = (term177 _86841 t s).
Proof. exact (eq_refl (term177 _86841 t s)). Qed.
Lemma lem3324768 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term56 _86841 s u t) = (term178 _86841 s u t).
Proof. exact (MK_COMB (@lem3324767 _86841 t s) (@lem3324758 _86841 u t)). Qed.
Lemma lem3324769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324770 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term59 _86841 s u t) = (term179 _86841 s u t).
Proof. exact (MK_COMB (@lem3324769) (@lem3324768 _86841 s u t)). Qed.
Lemma lem3324771 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term61 _86841 s u t x) = (term180 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324770 _86841 s u t) (@lem3324748 _86841 t x)). Qed.
Lemma lem3324772 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term70 _86841 s u x) = (term181 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324771 _86841 s u t x)). Qed.
Lemma lem3324773 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324774 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term71 _86841 s u x) = (term182 _86841 s u x).
Proof. exact (MK_COMB (@lem3324773 _86841) (@lem3324772 _86841 s u x)). Qed.
Lemma lem3324775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324776 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term86 _86841 s u x) = (term183 _86841 s u x).
Proof. exact (MK_COMB (@lem3324775) (@lem3324774 _86841 s u x)). Qed.
Lemma lem3324777 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term143 _86841 s u t x) = (term184 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324776 _86841 s u x) (@lem3324738 _86841 s u t x)). Qed.
Lemma lem3324778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3324783 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324784 {_86841 : Type'} (f : _86841 -> Prop) (x : _86841) : (f x) = (@I (_86841 -> Prop) f x).
Proof. exact (@lem3324783 _86841 Prop f x). Qed.
Lemma lem3324786 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (t x) = (@I (_86841 -> Prop) t x).
Proof. exact (@lem3324784 _86841 t x). Qed.
Lemma lem3324787 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (term57 _86841 t x) = (term174 _86841 t x).
Proof. exact (MK_COMB (@lem3324778) (@lem3324786 _86841 t x)). Qed.
Lemma lem3324788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3324793 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324794 {_86841 : Type'} (f : type686 _86841) (x : _86841 -> Prop) : (f x) = (@I ((_86841 -> Prop) -> Prop) f x).
Proof. exact (@lem3324793 (_86841 -> Prop) Prop f x). Qed.
Lemma lem3324796 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (u t) = (@I ((_86841 -> Prop) -> Prop) u t).
Proof. exact (@lem3324794 _86841 u t). Qed.
Lemma lem3324797 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (term175 _86841 u t) = (term176 _86841 u t).
Proof. exact (MK_COMB (@lem3324788) (@lem3324796 _86841 u t)). Qed.
Lemma lem3324798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324799 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (term185 _86841 u t) = (term186 _86841 u t).
Proof. exact (MK_COMB (@lem3324798) (@lem3324797 _86841 u t)). Qed.
Lemma lem3324800 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term73 _86841 u t x) = (term187 _86841 u t x).
Proof. exact (MK_COMB (@lem3324799 _86841 u t) (@lem3324787 _86841 t x)). Qed.
Lemma lem3324801 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term79 _86841 u x) = (term188 _86841 u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324800 _86841 u t x)). Qed.
Lemma lem3324802 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324803 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term80 _86841 u x) = (term189 _86841 u x).
Proof. exact (MK_COMB (@lem3324802 _86841) (@lem3324801 _86841 u x)). Qed.
Lemma lem3324804 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3324809 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324810 {_86841 : Type'} (f : _86841 -> Prop) (x : _86841) : (f x) = (@I (_86841 -> Prop) f x).
Proof. exact (@lem3324809 _86841 Prop f x). Qed.
Lemma lem3324812 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (s x) = (@I (_86841 -> Prop) s x).
Proof. exact (@lem3324810 _86841 s x). Qed.
Lemma lem3324813 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term57 _86841 s x) = (term174 _86841 s x).
Proof. exact (MK_COMB (@lem3324804) (@lem3324812 _86841 s x)). Qed.
Lemma lem3324814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324815 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term81 _86841 s x) = (term190 _86841 s x).
Proof. exact (MK_COMB (@lem3324814) (@lem3324813 _86841 s x)). Qed.
Lemma lem3324816 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term83 _86841 s u x) = (term191 _86841 s u x).
Proof. exact (MK_COMB (@lem3324815 _86841 s x) (@lem3324803 _86841 u x)). Qed.
Lemma lem3324821 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324822 {_86841 : Type'} (f : _86841 -> Prop) (x : _86841) : (f x) = (@I (_86841 -> Prop) f x).
Proof. exact (@lem3324821 _86841 Prop f x). Qed.
Lemma lem3324824 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (t x) = (@I (_86841 -> Prop) t x).
Proof. exact (@lem3324822 _86841 t x). Qed.
Lemma lem3324829 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3324830 {_86841 : Type'} (f : type686 _86841) (x : _86841 -> Prop) : (f x) = (@I ((_86841 -> Prop) -> Prop) f x).
Proof. exact (@lem3324829 (_86841 -> Prop) Prop f x). Qed.
Lemma lem3324832 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (u t) = (@I ((_86841 -> Prop) -> Prop) u t).
Proof. exact (@lem3324830 _86841 u t). Qed.
Lemma lem3324839 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) : (term8 _86841 t s) = (term8 _86841 t s).
Proof. exact (eq_refl (term8 _86841 t s)). Qed.
Lemma lem3324840 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term9 _86841 s u t) = (term192 _86841 s u t).
Proof. exact (MK_COMB (@lem3324839 _86841 t s) (@lem3324832 _86841 u t)). Qed.
Lemma lem3324841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324842 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) : (term11 _86841 s u t) = (term193 _86841 s u t).
Proof. exact (MK_COMB (@lem3324841) (@lem3324840 _86841 s u t)). Qed.
Lemma lem3324843 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term13 _86841 s u t x) = (term194 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324842 _86841 s u t) (@lem3324824 _86841 t x)). Qed.
Lemma lem3324844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3324845 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term108 _86841 s u t x) = (term195 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324844) (@lem3324843 _86841 s u t x)). Qed.
Lemma lem3324846 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term110 _86841 t s u x) = (term196 _86841 t s u x).
Proof. exact (MK_COMB (@lem3324845 _86841 s u t x) (@lem3324816 _86841 s u x)). Qed.
Lemma lem3324847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3324848 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term164 _86841 t s u x) = (term197 _86841 t s u x).
Proof. exact (MK_COMB (@lem3324847) (@lem3324846 _86841 t s u x)). Qed.
Lemma lem3324849 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term166 _86841 s u t x) = (term198 _86841 s u t x).
Proof. exact (MK_COMB (@lem3324848 _86841 t s u x) (@lem3324777 _86841 s u t x)). Qed.
Lemma lem3324850 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term166 _86841 s u t x) : term198 _86841 s u t x.
Proof. exact (EQ_MP (@lem3324849 _86841 s u t x) (@lem3324708 _86841 s u t x h1)). Qed.
Lemma lem3324851 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term196 _86841 t s u x.
Proof. exact (h1). Qed.
Lemma lem3324852 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term184 _86841 s u t x.
Proof. exact (h1). Qed.
Lemma lem3324853 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term191 _86841 s u x.
Proof. exact (proj2 (@lem3324851 _86841 t s u x h1)). Qed.
Lemma lem3324854 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term194 _86841 s u t x.
Proof. exact (proj1 (@lem3324851 _86841 t s u x h1)). Qed.
Lemma lem3324855 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term189 _86841 u x.
Proof. exact (proj2 (@lem3324853 _86841 t s u x h1)). Qed.
Lemma lem3324858 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term192 _86841 s u t.
Proof. exact (proj1 (@lem3324854 _86841 t s u x h1)). Qed.
Lemma lem3324861 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term173 _86841 s u t x.
Proof. exact (proj2 (@lem3324852 _86841 s u t x h1)). Qed.
Lemma lem3324862 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term182 _86841 s u x.
Proof. exact (proj1 (@lem3324852 _86841 s u t x h1)). Qed.
Lemma lem3324864 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : term171 _86841 u t x.
Proof. exact (h1). Qed.
Lemma lem3324891 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : t = s) : t = s.
Proof. exact (h1). Qed.
Lemma lem3324903 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term187 _86841 u t x) = (term187 _86841 u t x).
Proof. exact (eq_refl (term187 _86841 u t x)). Qed.
Lemma lem3324904 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term188 _86841 u x) = (term188 _86841 u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324903 _86841 u t x)). Qed.
Lemma lem3324905 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324907 {_86841 : Type'} (u : type686 _86841) (x : _86841) : (term189 _86841 u x) = (term189 _86841 u x).
Proof. exact (MK_COMB (@lem3324905 _86841) (@lem3324904 _86841 u x)). Qed.
Lemma lem3324908 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term189 _86841 u x.
Proof. exact (EQ_MP (@lem3324907 _86841 u x) (@lem3324855 _86841 t s u x h1)). Qed.
Lemma lem3324916 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (h1 : @I ((_86841 -> Prop) -> Prop) u t) : @I ((_86841 -> Prop) -> Prop) u t.
Proof. exact (h1). Qed.
Lemma lem3324934 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term180 _86841 s u t x) = (term199 _86841 s u t x).
Proof. exact (@lem19699 (term200 _86841 t s) (term176 _86841 u t) (term174 _86841 t x)). Qed.
Lemma lem3324935 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term181 _86841 s u x) = (term201 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324934 _86841 s u t x)). Qed.
Lemma lem3324936 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324938 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term182 _86841 s u x) = (term202 _86841 s u x).
Proof. exact (MK_COMB (@lem3324936 _86841) (@lem3324935 _86841 s u x)). Qed.
Lemma lem3324939 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term202 _86841 s u x.
Proof. exact (EQ_MP (@lem3324938 _86841 s u x) (@lem3324862 _86841 s u t x h1)). Qed.
Lemma lem3324943 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (h1 : @I (_86841 -> Prop) s x) : @I (_86841 -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3324961 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) : (term180 _86841 s u t x) = (term199 _86841 s u t x).
Proof. exact (@lem19699 (term200 _86841 t s) (term176 _86841 u t) (term174 _86841 t x)). Qed.
Lemma lem3324962 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term181 _86841 s u x) = (term201 _86841 s u x).
Proof. exact (fun_ext (fun t : _86841 -> Prop => @lem3324961 _86841 s u t x)). Qed.
Lemma lem3324963 {_86841 : Type'} : (@all (_86841 -> Prop)) = (@all (_86841 -> Prop)).
Proof. exact (eq_refl (@all (_86841 -> Prop))). Qed.
Lemma lem3324965 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term182 _86841 s u x) = (term202 _86841 s u x).
Proof. exact (MK_COMB (@lem3324963 _86841) (@lem3324962 _86841 s u x)). Qed.
Lemma lem3324966 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term202 _86841 s u x.
Proof. exact (EQ_MP (@lem3324965 _86841 s u x) (@lem3324862 _86841 s u t x h1)). Qed.
Lemma lem3324978 {_86841 : Type'} (_34502 : _86841 -> Prop) (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term203 _86841 u x _34502.
Proof. exact (@lem3324908 _86841 t s u x h1 _34502). Qed.
Lemma lem3324979 {_86841 : Type'} (u : type686 _86841) (_34502 : _86841 -> Prop) (x : _86841) : (term203 _86841 u x _34502) = (term187 _86841 u _34502 x).
Proof. exact (eq_refl (term203 _86841 u x _34502)). Qed.
Lemma lem3324981 {_86841 : Type'} (_34503 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term204 _86841 s u x _34503.
Proof. exact (@lem3324939 _86841 s u t x h1 _34503). Qed.
Lemma lem3324982 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (_34503 : _86841 -> Prop) (x : _86841) : (term204 _86841 s u x _34503) = (term199 _86841 s u _34503 x).
Proof. exact (eq_refl (term204 _86841 s u x _34503)). Qed.
Lemma lem3324983 {_86841 : Type'} (_34503 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term199 _86841 s u _34503 x.
Proof. exact (EQ_MP (@lem3324982 _86841 s u _34503 x) (@lem3324981 _86841 _34503 s u t x h1)). Qed.
Lemma lem3324984 {_86841 : Type'} (_34504 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term204 _86841 s u x _34504.
Proof. exact (@lem3324966 _86841 s u t x h1 _34504). Qed.
Lemma lem3324985 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (_34504 : _86841 -> Prop) (x : _86841) : (term204 _86841 s u x _34504) = (term199 _86841 s u _34504 x).
Proof. exact (eq_refl (term204 _86841 s u x _34504)). Qed.
Lemma lem3324986 {_86841 : Type'} (_34504 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term199 _86841 s u _34504 x.
Proof. exact (EQ_MP (@lem3324985 _86841 s u _34504 x) (@lem3324984 _86841 _34504 s u t x h1)). Qed.
Lemma lem3325000 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : @I (_86841 -> Prop) t x.
Proof. exact (proj2 (@lem3324854 _86841 t s u x h1)). Qed.
Lemma lem3325002 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : t = s) : t = s.
Proof. exact (h1). Qed.
Lemma lem3325010 {_86841 : Type'} (_34502 : _86841 -> Prop) (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term187 _86841 u _34502 x.
Proof. exact (EQ_MP (@lem3324979 _86841 u _34502 x) (@lem3324978 _86841 _34502 t s u x h1)). Qed.
Lemma lem3325014 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (h1 : @I ((_86841 -> Prop) -> Prop) u t) : @I ((_86841 -> Prop) -> Prop) u t.
Proof. exact (h1). Qed.
Lemma lem3325016 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (h1 : @I (_86841 -> Prop) s x) : @I (_86841 -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3325022 {_86841 : Type'} (_34503 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term205 _86841 s _34503 x.
Proof. exact (proj1 (@lem3324983 _86841 _34503 s u t x h1)). Qed.
Lemma lem3325044 {_86841 : Type'} (_34504 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term187 _86841 u _34504 x.
Proof. exact (proj2 (@lem3324986 _86841 _34504 s u t x h1)). Qed.
Lemma lem3325072 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term174 _86841 s x.
Proof. exact (proj1 (@lem3324853 _86841 t s u x h1)). Qed.
Lemma lem3325087 {_86841 : Type'} (x : _86841) : (term206 _86841 x) = (term206 _86841 x).
Proof. exact (eq_refl (term206 _86841 x)). Qed.
Lemma lem3325088 {_86841 : Type'} (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : t = s) : (term207 _86841 x t) = (term207 _86841 x s).
Proof. exact (MK_COMB (@lem3325087 _86841 x) (@lem3325002 _86841 t s h1)). Qed.
Lemma lem3325089 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term207 _86841 x s) = (@I (_86841 -> Prop) s x).
Proof. exact (eq_refl (term207 _86841 x s)). Qed.
Lemma lem3325090 {_86841 : Type'} (x : _86841) (t : _86841 -> Prop) : (term208 _86841 x t) = (term208 _86841 x t).
Proof. exact (eq_refl (term208 _86841 x t)). Qed.
Lemma lem3325091 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) : ((term207 _86841 x t) = (term207 _86841 x s)) = ((term207 _86841 x t) = (@I (_86841 -> Prop) s x)).
Proof. exact (MK_COMB (@lem3325090 _86841 x t) (@lem3325089 _86841 s x)). Qed.
Lemma lem3325092 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (term207 _86841 x t) = (@I (_86841 -> Prop) t x).
Proof. exact (eq_refl (term207 _86841 x t)). Qed.
Lemma lem3325093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3325094 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (term208 _86841 x t) = (term209 _86841 t x).
Proof. exact (MK_COMB (@lem3325093) (@lem3325092 _86841 t x)). Qed.
Lemma lem3325095 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (@I (_86841 -> Prop) s x) = (@I (_86841 -> Prop) s x).
Proof. exact (eq_refl (@I (_86841 -> Prop) s x)). Qed.
Lemma lem3325096 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) : ((term207 _86841 x t) = (@I (_86841 -> Prop) s x)) = ((@I (_86841 -> Prop) t x) = (@I (_86841 -> Prop) s x)).
Proof. exact (MK_COMB (@lem3325094 _86841 t x) (@lem3325095 _86841 s x)). Qed.
Lemma lem3325097 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) : ((term207 _86841 x t) = (term207 _86841 x s)) = ((@I (_86841 -> Prop) t x) = (@I (_86841 -> Prop) s x)).
Proof. exact (TRANS (@lem3325091 _86841 t s x) (@lem3325096 _86841 t s x)). Qed.
Lemma lem3325098 {_86841 : Type'} (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : t = s) : (@I (_86841 -> Prop) t x) = (@I (_86841 -> Prop) s x).
Proof. exact (EQ_MP (@lem3325097 _86841 t s x) (@lem3325088 _86841 x t s h1)). Qed.
Lemma lem3325101 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : @I (_86841 -> Prop) s x.
Proof. exact (EQ_MP (@lem3325098 _86841 x t s h2) (@lem3325000 _86841 t s u x h1)). Qed.
Lemma lem3325102 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : term210 _86841 s x.
Proof. exact (fun h0 : term174 _86841 s x => @lem3325101 _86841 u x t s h1 h2). Qed.
Lemma lem3325104 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325105 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term210 _86841 s x) = (@I (_86841 -> Prop) s x).
Proof. exact (@lem3325104 (@I (_86841 -> Prop) s x)). Qed.
Lemma lem3325106 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : @I (_86841 -> Prop) s x.
Proof. exact (EQ_MP (@lem3325105 _86841 s x) (@lem3325102 _86841 u x t s h1 h2)). Qed.
Lemma lem3325109 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3325111 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term174 _86841 s x) = (term212 _86841 s x).
Proof. exact (@lem3325109 (@I (_86841 -> Prop) s x)). Qed.
Lemma lem3325114 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term212 _86841 s x.
Proof. exact (EQ_MP (@lem3325111 _86841 s x) (@lem3325072 _86841 t s u x h1)). Qed.
Lemma lem3325117 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : False.
Proof. exact (@lem3325114 _86841 t s u x h1 (@lem3325106 _86841 u x t s h1 h2)). Qed.
Lemma lem3325118 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : term213.
Proof. exact (fun h0 : ~ False => @lem3325117 _86841 u x t s h1 h2). Qed.
Lemma lem3325120 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325121 : term213 = False.
Proof. exact (@lem3325120 False). Qed.
Lemma lem3325124 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (h1 : @I ((_86841 -> Prop) -> Prop) u t) : @I ((_86841 -> Prop) -> Prop) u t.
Proof. exact (h1). Qed.
Lemma lem3325125 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (h1 : @I ((_86841 -> Prop) -> Prop) u t) : term214 _86841 u t.
Proof. exact (fun h0 : term176 _86841 u t => @lem3325124 _86841 u t h1). Qed.
Lemma lem3325127 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325128 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (term214 _86841 u t) = (@I ((_86841 -> Prop) -> Prop) u t).
Proof. exact (@lem3325127 (@I ((_86841 -> Prop) -> Prop) u t)). Qed.
Lemma lem3325129 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (h1 : @I ((_86841 -> Prop) -> Prop) u t) : @I ((_86841 -> Prop) -> Prop) u t.
Proof. exact (EQ_MP (@lem3325128 _86841 u t) (@lem3325125 _86841 u t h1)). Qed.
Lemma lem3325131 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : @I (_86841 -> Prop) t x.
Proof. exact (proj2 (@lem3324854 _86841 t s u x h1)). Qed.
Lemma lem3325132 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term210 _86841 t x.
Proof. exact (fun h0 : term174 _86841 t x => @lem3325131 _86841 t s u x h1). Qed.
Lemma lem3325134 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325135 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (term210 _86841 t x) = (@I (_86841 -> Prop) t x).
Proof. exact (@lem3325134 (@I (_86841 -> Prop) t x)). Qed.
Lemma lem3325136 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : @I (_86841 -> Prop) t x.
Proof. exact (EQ_MP (@lem3325135 _86841 t x) (@lem3325132 _86841 t s u x h1)). Qed.
Lemma lem3325138 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3325139 {_86841 : Type'} (u : type686 _86841) (_34502 : _86841 -> Prop) (x : _86841) : (term187 _86841 u _34502 x) = (term217 _86841 u _34502 x).
Proof. exact (@lem3325138 (@I ((_86841 -> Prop) -> Prop) u _34502) (@I (_86841 -> Prop) _34502 x)). Qed.
Lemma lem3325141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3325142 {_86841 : Type'} (u : type686 _86841) (_34502 : _86841 -> Prop) (x : _86841) : (term217 _86841 u _34502 x) = (term218 _86841 u _34502 x).
Proof. exact (@lem3325141 (term171 _86841 u _34502 x)). Qed.
Lemma lem3325143 {_86841 : Type'} (u : type686 _86841) (_34502 : _86841 -> Prop) (x : _86841) : (term187 _86841 u _34502 x) = (term218 _86841 u _34502 x).
Proof. exact (TRANS (@lem3325139 _86841 u _34502 x) (@lem3325142 _86841 u _34502 x)). Qed.
Lemma lem3325145 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : term171 _86841 u t x.
Proof. exact (conj (@lem3325129 _86841 u t h2) (@lem3325136 _86841 t s u x h1)). Qed.
Lemma lem3325147 {_86841 : Type'} (_34502 : _86841 -> Prop) (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term218 _86841 u _34502 x.
Proof. exact (EQ_MP (@lem3325143 _86841 u _34502 x) (@lem3325010 _86841 _34502 t s u x h1)). Qed.
Lemma lem3325148 {_86841 : Type'} (_34502 : _86841 -> Prop) (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term218 _86841 u _34502 x.
Proof. exact (@lem3325147 _86841 _34502 t s u x h1). Qed.
Lemma lem3325149 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : term218 _86841 u t x.
Proof. exact (@lem3325148 _86841 t t s u x h1). Qed.
Lemma lem3325152 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : False.
Proof. exact (@lem3325149 _86841 t s u x h1 (@lem3325145 _86841 s x u t h1 h2)). Qed.
Lemma lem3325153 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : term213.
Proof. exact (fun h0 : ~ False => @lem3325152 _86841 s x u t h1 h2). Qed.
Lemma lem3325155 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325156 : term213 = False.
Proof. exact (@lem3325155 False). Qed.
Lemma lem3325157 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3325156) (@lem3325153 _86841 s x u t h1 h2)). Qed.
Lemma lem3325203 {_86841 : Type'} (x : _86841 -> Prop) : x = x.
Proof. exact (@lem21386 (_86841 -> Prop) x). Qed.
Lemma lem3325204 {_86841 : Type'} (x : _86841 -> Prop) : x = x.
Proof. exact (@lem3325203 _86841 x). Qed.
Lemma lem3325205 {_86841 : Type'} (s : _86841 -> Prop) : s = s.
Proof. exact (@lem3325204 _86841 s). Qed.
Lemma lem3325206 {_86841 : Type'} (s : _86841 -> Prop) : term219 _86841 s.
Proof. exact (fun h0 : term220 _86841 s => @lem3325205 _86841 s). Qed.
Lemma lem3325208 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325209 {_86841 : Type'} (s : _86841 -> Prop) : (term219 _86841 s) = (s = s).
Proof. exact (@lem3325208 (s = s)). Qed.
Lemma lem3325210 {_86841 : Type'} (s : _86841 -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3325209 _86841 s) (@lem3325206 _86841 s)). Qed.
Lemma lem3325212 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (h1 : @I (_86841 -> Prop) s x) : @I (_86841 -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3325213 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (h1 : @I (_86841 -> Prop) s x) : term210 _86841 s x.
Proof. exact (fun h0 : term174 _86841 s x => @lem3325212 _86841 s x h1). Qed.
Lemma lem3325215 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325216 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) : (term210 _86841 s x) = (@I (_86841 -> Prop) s x).
Proof. exact (@lem3325215 (@I (_86841 -> Prop) s x)). Qed.
Lemma lem3325217 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (h1 : @I (_86841 -> Prop) s x) : @I (_86841 -> Prop) s x.
Proof. exact (EQ_MP (@lem3325216 _86841 s x) (@lem3325213 _86841 s x h1)). Qed.
Lemma lem3325219 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3325220 {_86841 : Type'} (s : _86841 -> Prop) (_34503 : _86841 -> Prop) (x : _86841) : (term205 _86841 s _34503 x) = (term221 _86841 s _34503 x).
Proof. exact (@lem3325219 (_34503 = s) (@I (_86841 -> Prop) _34503 x)). Qed.
Lemma lem3325222 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3325223 {_86841 : Type'} (s : _86841 -> Prop) (_34503 : _86841 -> Prop) (x : _86841) : (term221 _86841 s _34503 x) = (term222 _86841 s _34503 x).
Proof. exact (@lem3325222 (term223 _86841 s _34503 x)). Qed.
Lemma lem3325224 {_86841 : Type'} (s : _86841 -> Prop) (_34503 : _86841 -> Prop) (x : _86841) : (term205 _86841 s _34503 x) = (term222 _86841 s _34503 x).
Proof. exact (TRANS (@lem3325220 _86841 s _34503 x) (@lem3325223 _86841 s _34503 x)). Qed.
Lemma lem3325226 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (h1 : @I (_86841 -> Prop) s x) : term224 _86841 s x.
Proof. exact (conj (@lem3325210 _86841 s) (@lem3325217 _86841 s x h1)). Qed.
Lemma lem3325228 {_86841 : Type'} (_34503 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term222 _86841 s _34503 x.
Proof. exact (EQ_MP (@lem3325224 _86841 s _34503 x) (@lem3325022 _86841 _34503 s u t x h1)). Qed.
Lemma lem3325229 {_86841 : Type'} (_34503 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term222 _86841 s _34503 x.
Proof. exact (@lem3325228 _86841 _34503 s u t x h1). Qed.
Lemma lem3325230 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term225 _86841 s x.
Proof. exact (@lem3325229 _86841 s s u t x h1). Qed.
Lemma lem3325233 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : False.
Proof. exact (@lem3325230 _86841 s u t x h1 (@lem3325226 _86841 s x h2)). Qed.
Lemma lem3325234 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : term213.
Proof. exact (fun h0 : ~ False => @lem3325233 _86841 u t s x h1 h2). Qed.
Lemma lem3325236 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325237 : term213 = False.
Proof. exact (@lem3325236 False). Qed.
Lemma lem3325238 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3325237) (@lem3325234 _86841 u t s x h1 h2)). Qed.
Lemma lem3325284 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : @I ((_86841 -> Prop) -> Prop) u t.
Proof. exact (proj1 (@lem3324864 _86841 u t x h1)). Qed.
Lemma lem3325285 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : term214 _86841 u t.
Proof. exact (fun h0 : term176 _86841 u t => @lem3325284 _86841 u t x h1). Qed.
Lemma lem3325287 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325288 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) : (term214 _86841 u t) = (@I ((_86841 -> Prop) -> Prop) u t).
Proof. exact (@lem3325287 (@I ((_86841 -> Prop) -> Prop) u t)). Qed.
Lemma lem3325289 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : @I ((_86841 -> Prop) -> Prop) u t.
Proof. exact (EQ_MP (@lem3325288 _86841 u t) (@lem3325285 _86841 u t x h1)). Qed.
Lemma lem3325291 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : @I (_86841 -> Prop) t x.
Proof. exact (proj2 (@lem3324864 _86841 u t x h1)). Qed.
Lemma lem3325292 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : term210 _86841 t x.
Proof. exact (fun h0 : term174 _86841 t x => @lem3325291 _86841 u t x h1). Qed.
Lemma lem3325294 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325295 {_86841 : Type'} (t : _86841 -> Prop) (x : _86841) : (term210 _86841 t x) = (@I (_86841 -> Prop) t x).
Proof. exact (@lem3325294 (@I (_86841 -> Prop) t x)). Qed.
Lemma lem3325296 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : @I (_86841 -> Prop) t x.
Proof. exact (EQ_MP (@lem3325295 _86841 t x) (@lem3325292 _86841 u t x h1)). Qed.
Lemma lem3325298 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3325299 {_86841 : Type'} (u : type686 _86841) (_34504 : _86841 -> Prop) (x : _86841) : (term187 _86841 u _34504 x) = (term217 _86841 u _34504 x).
Proof. exact (@lem3325298 (@I ((_86841 -> Prop) -> Prop) u _34504) (@I (_86841 -> Prop) _34504 x)). Qed.
Lemma lem3325301 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3325302 {_86841 : Type'} (u : type686 _86841) (_34504 : _86841 -> Prop) (x : _86841) : (term217 _86841 u _34504 x) = (term218 _86841 u _34504 x).
Proof. exact (@lem3325301 (term171 _86841 u _34504 x)). Qed.
Lemma lem3325303 {_86841 : Type'} (u : type686 _86841) (_34504 : _86841 -> Prop) (x : _86841) : (term187 _86841 u _34504 x) = (term218 _86841 u _34504 x).
Proof. exact (TRANS (@lem3325299 _86841 u _34504 x) (@lem3325302 _86841 u _34504 x)). Qed.
Lemma lem3325305 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term171 _86841 u t x) : term171 _86841 u t x.
Proof. exact (conj (@lem3325289 _86841 u t x h1) (@lem3325296 _86841 u t x h1)). Qed.
Lemma lem3325307 {_86841 : Type'} (_34504 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term218 _86841 u _34504 x.
Proof. exact (EQ_MP (@lem3325303 _86841 u _34504 x) (@lem3325044 _86841 _34504 s u t x h1)). Qed.
Lemma lem3325308 {_86841 : Type'} (_34504 : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term218 _86841 u _34504 x.
Proof. exact (@lem3325307 _86841 _34504 s u t x h1). Qed.
Lemma lem3325309 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : term218 _86841 u t x.
Proof. exact (@lem3325308 _86841 t s u t x h1). Qed.
Lemma lem3325312 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : term171 _86841 u t x) : False.
Proof. exact (@lem3325309 _86841 s u t x h1 (@lem3325305 _86841 u t x h2)). Qed.
Lemma lem3325313 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : term171 _86841 u t x) : term213.
Proof. exact (fun h0 : ~ False => @lem3325312 _86841 s u t x h1 h2). Qed.
Lemma lem3325315 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3325316 : term213 = False.
Proof. exact (@lem3325315 False). Qed.
Lemma lem3325317 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : term171 _86841 u t x) : False.
Proof. exact (EQ_MP (@lem3325316) (@lem3325313 _86841 s u t x h1 h2)). Qed.
Lemma lem3325318 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3325121) (@lem3325118 _86841 u x t s h1 h2)). Qed.
Lemma lem3325319 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : (@I (_86841 -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86841 -> Prop) s x => @lem3325238 _86841 u t s x h1 h2) (fun h3 : False => @lem3325016 _86841 s x h2)). Qed.
Lemma lem3325320 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3325319 _86841 u t s x h1 h2) (@lem3325016 _86841 s x h2)). Qed.
Lemma lem3325321 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : (@I ((_86841 -> Prop) -> Prop) u t) = False.
Proof. exact (prop_ext (fun h3 : @I ((_86841 -> Prop) -> Prop) u t => @lem3325157 _86841 s x u t h1 h2) (fun h3 : False => @lem3325014 _86841 u t h2)). Qed.
Lemma lem3325322 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3325321 _86841 s x u t h1 h2) (@lem3325014 _86841 u t h2)). Qed.
Lemma lem3325323 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : (t = s) = False.
Proof. exact (prop_ext (fun h3 : t = s => @lem3325318 _86841 u x t s h1 h2) (fun h3 : False => @lem3325002 _86841 t s h2)). Qed.
Lemma lem3325324 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3325323 _86841 u x t s h1 h2) (@lem3325002 _86841 t s h2)). Qed.
Lemma lem3325325 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : (@I (_86841 -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86841 -> Prop) s x => @lem3325320 _86841 u t s x h1 h2) (fun h3 : False => @lem3324943 _86841 s x h2)). Qed.
Lemma lem3325326 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3325325 _86841 u t s x h1 h2) (@lem3324943 _86841 s x h2)). Qed.
Lemma lem3325327 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : (@I ((_86841 -> Prop) -> Prop) u t) = False.
Proof. exact (prop_ext (fun h3 : @I ((_86841 -> Prop) -> Prop) u t => @lem3325322 _86841 s x u t h1 h2) (fun h3 : False => @lem3324916 _86841 u t h2)). Qed.
Lemma lem3325328 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3325327 _86841 s x u t h1 h2) (@lem3324916 _86841 u t h2)). Qed.
Lemma lem3325329 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : (t = s) = False.
Proof. exact (prop_ext (fun h3 : t = s => @lem3325324 _86841 u x t s h1 h2) (fun h3 : False => @lem3324891 _86841 t s h2)). Qed.
Lemma lem3325330 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3325329 _86841 u x t s h1 h2) (@lem3324891 _86841 t s h2)). Qed.
Lemma lem3325331 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : (@I (_86841 -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86841 -> Prop) s x => @lem3325326 _86841 u t s x h1 h2) (fun h3 : False => @lem3324943 _86841 s x h2)). Qed.
Lemma lem3325332 {_86841 : Type'} (u : type686 _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) (h2 : @I (_86841 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3325331 _86841 u t s x h1 h2) (@lem3324943 _86841 s x h2)). Qed.
Lemma lem3325333 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : (@I ((_86841 -> Prop) -> Prop) u t) = False.
Proof. exact (prop_ext (fun h3 : @I ((_86841 -> Prop) -> Prop) u t => @lem3325328 _86841 s x u t h1 h2) (fun h3 : False => @lem3324916 _86841 u t h2)). Qed.
Lemma lem3325334 {_86841 : Type'} (s : _86841 -> Prop) (x : _86841) (u : type686 _86841) (t : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : @I ((_86841 -> Prop) -> Prop) u t) : False.
Proof. exact (EQ_MP (@lem3325333 _86841 s x u t h1 h2) (@lem3324916 _86841 u t h2)). Qed.
Lemma lem3325335 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : (t = s) = False.
Proof. exact (prop_ext (fun h3 : t = s => @lem3325330 _86841 u x t s h1 h2) (fun h3 : False => @lem3324891 _86841 t s h2)). Qed.
Lemma lem3325336 {_86841 : Type'} (u : type686 _86841) (x : _86841) (t : _86841 -> Prop) (s : _86841 -> Prop) (h1 : term196 _86841 t s u x) (h2 : t = s) : False.
Proof. exact (EQ_MP (@lem3325335 _86841 u x t s h1 h2) (@lem3324891 _86841 t s h2)). Qed.
Lemma lem3325337 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term184 _86841 s u t x) : False.
Proof. exact (or_elim (@lem3324861 _86841 s u t x h1) (fun h0 : @I (_86841 -> Prop) s x => @lem3325332 _86841 u t s x h1 h0) (fun h0 : term171 _86841 u t x => @lem3325317 _86841 s u t x h1 h0)). Qed.
Lemma lem3325338 {_86841 : Type'} (t : _86841 -> Prop) (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term196 _86841 t s u x) : False.
Proof. exact (or_elim (@lem3324858 _86841 t s u x h1) (fun h0 : t = s => @lem3325336 _86841 u x t s h1 h0) (fun h0 : @I ((_86841 -> Prop) -> Prop) u t => @lem3325334 _86841 s x u t h1 h0)). Qed.
Lemma lem3325339 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (t : _86841 -> Prop) (x : _86841) (h1 : term166 _86841 s u t x) : False.
Proof. exact (or_elim (@lem3324850 _86841 s u t x h1) (fun h0 : term196 _86841 t s u x => @lem3325338 _86841 t s u x h0) (fun h0 : term184 _86841 s u t x => @lem3325337 _86841 s u t x h0)). Qed.
Lemma lem3325340 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term54 _86841 s u x) : False.
Proof. exact (ex_elim (@lem3324707 _86841 s u x h1) (fun t : _86841 -> Prop => fun h0 : term168 _86841 s u x t => @lem3325339 _86841 s u t x h0)). Qed.
Lemma lem3325341 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term54 _86841 s u x) : (term54 _86841 s u x) = False.
Proof. exact (prop_ext (fun h2 : term54 _86841 s u x => @lem3325340 _86841 s u x h1) (fun h2 : False => @lem3324352 _86841 s u x h1)). Qed.
Lemma lem3325342 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) (h1 : term54 _86841 s u x) : False.
Proof. exact (EQ_MP (@lem3325341 _86841 s u x h1) (@lem3324352 _86841 s u x h1)). Qed.
Lemma lem3325343 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : term53 _86841 s u x.
Proof. exact (fun h0 : term54 _86841 s u x => @lem3325342 _86841 s u x h0). Qed.
Lemma lem3325344 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (x : _86841) : (term16 _86841 s u x) = (term32 _86841 s u x).
Proof. exact (EQ_MP (@lem3324351 _86841 s u x) (@lem3325343 _86841 s u x)). Qed.
Lemma lem3325349 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term36 _86841 s u.
Proof. exact (fun x : _86841 => @lem3325344 _86841 s u x). Qed.
Lemma lem3325354 {_86841 : Type'} (u : type686 _86841) : term48 _86841 u.
Proof. exact (fun s : _86841 -> Prop => @lem3325349 _86841 s u). Qed.
Lemma lem3325359 {_86841 : Type'} : term52 _86841.
Proof. exact (fun u : type686 _86841 => @lem3325354 _86841 u). Qed.
Lemma lem3325360 {_86841 : Type'} : term51 _86841.
Proof. exact (EQ_MP (@lem3324347 _86841) (@lem3325359 _86841)). Qed.
Lemma lem3325361 {_86841 : Type'} (u : type686 _86841) : term226 _86841 u.
Proof. exact (@lem3325360 _86841 u). Qed.
Lemma lem3325362 {_86841 : Type'} (u : type686 _86841) : (term226 _86841 u) = (term47 _86841 u).
Proof. exact (eq_refl (term226 _86841 u)). Qed.
Lemma lem3325363 {_86841 : Type'} (u : type686 _86841) : term47 _86841 u.
Proof. exact (EQ_MP (@lem3325362 _86841 u) (@lem3325361 _86841 u)). Qed.
Lemma lem3325364 {_86841 : Type'} (u : type686 _86841) (s : _86841 -> Prop) : term227 _86841 u s.
Proof. exact (@lem3325363 _86841 u s). Qed.
Lemma lem3325365 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term227 _86841 u s) = (term38 _86841 s u).
Proof. exact (eq_refl (term227 _86841 u s)). Qed.
Lemma lem3325366 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term38 _86841 s u.
Proof. exact (EQ_MP (@lem3325365 _86841 s u) (@lem3325364 _86841 u s)). Qed.
Lemma lem3325368 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term38 _86841 s u.
Proof. exact (@lem3324148 _86841 s u (@lem3325366 _86841 s u)). Qed.
Lemma lem3325369 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term39 _86841 s u) : False.
Proof. exact (@lem3325368 _86841 s u (@lem3324132 _86841 s u h1)). Qed.
Lemma lem3325370 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term39 _86841 s u) : (term39 _86841 s u) = False.
Proof. exact (prop_ext (fun h2 : term39 _86841 s u => @lem3325369 _86841 s u h1) (fun h2 : False => @lem3324132 _86841 s u h1)). Qed.
Lemma lem3325371 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) (h1 : term39 _86841 s u) : False.
Proof. exact (EQ_MP (@lem3325370 _86841 s u h1) (@lem3324132 _86841 s u h1)). Qed.
Lemma lem3325372 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term38 _86841 s u.
Proof. exact (fun h0 : term39 _86841 s u => @lem3325371 _86841 s u h0). Qed.
Lemma lem3325373 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term36 _86841 s u.
Proof. exact (EQ_MP (@lem3324131 _86841 s u) (@lem3325372 _86841 s u)). Qed.
Lemma lem3325374 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : term35 _86841 s u.
Proof. exact (EQ_MP (@lem3324127 _86841 s u) (@lem3325373 _86841 s u)). Qed.
