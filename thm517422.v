Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm517422_term_abbrevs.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem516990 (n : nat) : term0 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem516991 (n : nat) : (term0 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem516993 (n : nat) : term1 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem516994 (n : nat) : (term1 n) = ((BIT1 n) = (term2 n)).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem516996 (n : nat) : term3 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem516997 (n : nat) : (term3 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem517012 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516997 n) (@lem516996 n)). Qed.
Lemma lem517013 (m : nat) : (NUMERAL m) = m.
Proof. exact (@lem517012 m). Qed.
Lemma lem517014 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517015 (m : nat) : (term4 m) = (Peano.le m).
Proof. exact (MK_COMB (@lem517014) (@lem517013 m)). Qed.
Lemma lem517017 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516997 n) (@lem516996 n)). Qed.
Lemma lem517018 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (MK_COMB (@lem517015 m) (@lem517017 n)). Qed.
Lemma lem517019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517020 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem517019) (@lem517018 m n)). Qed.
Lemma lem517021 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem517022 (m : nat) (n : nat) : ((term5 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem517020 m n) (@lem517021 m n)). Qed.
Lemma lem517024 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem517025 (x : Prop) : (x = x) = True.
Proof. exact (@lem517024 Prop x). Qed.
Lemma lem517026 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem517025 (Peano.le m n)). Qed.
Lemma lem517027 (m : nat) (n : nat) : ((term5 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem517022 m n) (@lem517026 m n)). Qed.
Lemma lem517028 (m : nat) : (term8 m) = term9.
Proof. exact (fun_ext (fun n : nat => @lem517027 m n)). Qed.
Lemma lem517029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517030 (m : nat) : (term10 m) = term11.
Proof. exact (MK_COMB (@lem517029) (@lem517028 m)). Qed.
Lemma lem517032 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem517033 (t : Prop) : (term13 t) = t.
Proof. exact (@lem517032 nat t). Qed.
Lemma lem517034 : term11 = True.
Proof. exact (@lem517033 True). Qed.
Lemma lem517035 (m : nat) : (term10 m) = True.
Proof. exact (TRANS (@lem517030 m) (@lem517034)). Qed.
Lemma lem517036 : term14 = term9.
Proof. exact (fun_ext (fun m : nat => @lem517035 m)). Qed.
Lemma lem517037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517038 : term15 = term11.
Proof. exact (MK_COMB (@lem517037) (@lem517036)). Qed.
Lemma lem517040 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem517041 (t : Prop) : (term13 t) = t.
Proof. exact (@lem517040 nat t). Qed.
Lemma lem517042 : term11 = True.
Proof. exact (@lem517041 True). Qed.
Lemma lem517043 : term15 = True.
Proof. exact (TRANS (@lem517038) (@lem517042)). Qed.
Lemma lem517044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517045 : term16 = (and True).
Proof. exact (MK_COMB (@lem517044) (@lem517043)). Qed.
Lemma lem517049 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem517050 : ((Peano.le 0 0) = True) = (Peano.le 0 0).
Proof. exact (@lem517049 (Peano.le 0 0)). Qed.
Lemma lem517051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517052 : term17 = term18.
Proof. exact (MK_COMB (@lem517051) (@lem517050)). Qed.
Lemma lem517062 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516991 n) (@lem516990 n)). Qed.
Lemma lem517063 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517064 (n : nat) : (term19 n) = (term20 n).
Proof. exact (MK_COMB (@lem517063) (@lem517062 n)). Qed.
Lemma lem517065 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem517066 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem517064 n) (@lem517065)). Qed.
Lemma lem517067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517068 (n : nat) : (term23 n) = (term24 n).
Proof. exact (MK_COMB (@lem517067) (@lem517066 n)). Qed.
Lemma lem517069 (n : nat) : (Peano.le n 0) = (Peano.le n 0).
Proof. exact (eq_refl (Peano.le n 0)). Qed.
Lemma lem517070 (n : nat) : ((term21 n) = (Peano.le n 0)) = ((term22 n) = (Peano.le n 0)).
Proof. exact (MK_COMB (@lem517068 n) (@lem517069 n)). Qed.
Lemma lem517073 : term25 = term26.
Proof. exact (fun_ext (fun n : nat => @lem517070 n)). Qed.
Lemma lem517074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517075 : term27 = term28.
Proof. exact (MK_COMB (@lem517074) (@lem517073)). Qed.
Lemma lem517080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517081 : term29 = term30.
Proof. exact (MK_COMB (@lem517080) (@lem517075)). Qed.
Lemma lem517089 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem517090 (n : nat) : ((term31 n) = False) = (term32 n).
Proof. exact (@lem517089 (term31 n)). Qed.
Lemma lem517092 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (EQ_MP (@lem516994 n) (@lem516993 n)). Qed.
Lemma lem517093 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517094 (n : nat) : (term33 n) = (term34 n).
Proof. exact (MK_COMB (@lem517093) (@lem517092 n)). Qed.
Lemma lem517095 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem517096 (n : nat) : (term31 n) = (term35 n).
Proof. exact (MK_COMB (@lem517094 n) (@lem517095)). Qed.
Lemma lem517097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem517098 (n : nat) : (term32 n) = (term36 n).
Proof. exact (MK_COMB (@lem517097) (@lem517096 n)). Qed.
Lemma lem517099 (n : nat) : ((term31 n) = False) = (term36 n).
Proof. exact (TRANS (@lem517090 n) (@lem517098 n)). Qed.
Lemma lem517100 : term37 = term38.
Proof. exact (fun_ext (fun n : nat => @lem517099 n)). Qed.
Lemma lem517101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517102 : term39 = term40.
Proof. exact (MK_COMB (@lem517101) (@lem517100)). Qed.
Lemma lem517107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517108 : term41 = term42.
Proof. exact (MK_COMB (@lem517107) (@lem517102)). Qed.
Lemma lem517116 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem517117 (n : nat) : ((term43 n) = True) = (term43 n).
Proof. exact (@lem517116 (term43 n)). Qed.
Lemma lem517119 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516991 n) (@lem516990 n)). Qed.
Lemma lem517120 : (Peano.le 0) = (Peano.le 0).
Proof. exact (eq_refl (Peano.le 0)). Qed.
Lemma lem517121 (n : nat) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem517120) (@lem517119 n)). Qed.
Lemma lem517122 (n : nat) : ((term43 n) = True) = (term44 n).
Proof. exact (TRANS (@lem517117 n) (@lem517121 n)). Qed.
Lemma lem517123 : term45 = term46.
Proof. exact (fun_ext (fun n : nat => @lem517122 n)). Qed.
Lemma lem517124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517125 : term47 = term48.
Proof. exact (MK_COMB (@lem517124) (@lem517123)). Qed.
Lemma lem517130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517131 : term49 = term50.
Proof. exact (MK_COMB (@lem517130) (@lem517125)). Qed.
Lemma lem517139 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem517140 (n : nat) : ((term51 n) = True) = (term51 n).
Proof. exact (@lem517139 (term51 n)). Qed.
Lemma lem517142 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (EQ_MP (@lem516994 n) (@lem516993 n)). Qed.
Lemma lem517143 : (Peano.le 0) = (Peano.le 0).
Proof. exact (eq_refl (Peano.le 0)). Qed.
Lemma lem517144 (n : nat) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem517143) (@lem517142 n)). Qed.
Lemma lem517145 (n : nat) : ((term51 n) = True) = (term52 n).
Proof. exact (TRANS (@lem517140 n) (@lem517144 n)). Qed.
Lemma lem517146 : term53 = term54.
Proof. exact (fun_ext (fun n : nat => @lem517145 n)). Qed.
Lemma lem517147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517148 : term55 = term56.
Proof. exact (MK_COMB (@lem517147) (@lem517146)). Qed.
Lemma lem517153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517154 : term57 = term58.
Proof. exact (MK_COMB (@lem517153) (@lem517148)). Qed.
Lemma lem517168 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516991 n) (@lem516990 n)). Qed.
Lemma lem517169 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem517168 m). Qed.
Lemma lem517170 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517171 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem517170) (@lem517169 m)). Qed.
Lemma lem517173 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516991 n) (@lem516990 n)). Qed.
Lemma lem517174 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem517171 m) (@lem517173 n)). Qed.
Lemma lem517175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517176 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem517175) (@lem517174 m n)). Qed.
Lemma lem517177 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem517178 (m : nat) (n : nat) : ((term59 m n) = (Peano.le m n)) = ((term60 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem517176 m n) (@lem517177 m n)). Qed.
Lemma lem517181 (m : nat) : (term63 m) = (term64 m).
Proof. exact (fun_ext (fun n : nat => @lem517178 m n)). Qed.
Lemma lem517182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517183 (m : nat) : (term65 m) = (term66 m).
Proof. exact (MK_COMB (@lem517182) (@lem517181 m)). Qed.
Lemma lem517188 : term67 = term68.
Proof. exact (fun_ext (fun m : nat => @lem517183 m)). Qed.
Lemma lem517189 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517190 : term69 = term70.
Proof. exact (MK_COMB (@lem517189) (@lem517188)). Qed.
Lemma lem517195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517196 : term71 = term72.
Proof. exact (MK_COMB (@lem517195) (@lem517190)). Qed.
Lemma lem517210 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516991 n) (@lem516990 n)). Qed.
Lemma lem517211 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem517210 m). Qed.
Lemma lem517212 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517213 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem517212) (@lem517211 m)). Qed.
Lemma lem517215 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (EQ_MP (@lem516994 n) (@lem516993 n)). Qed.
Lemma lem517216 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (MK_COMB (@lem517213 m) (@lem517215 n)). Qed.
Lemma lem517217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517218 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem517217) (@lem517216 m n)). Qed.
Lemma lem517219 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem517220 (m : nat) (n : nat) : ((term73 m n) = (Peano.le m n)) = ((term74 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem517218 m n) (@lem517219 m n)). Qed.
Lemma lem517223 (m : nat) : (term77 m) = (term78 m).
Proof. exact (fun_ext (fun n : nat => @lem517220 m n)). Qed.
Lemma lem517224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517225 (m : nat) : (term79 m) = (term80 m).
Proof. exact (MK_COMB (@lem517224) (@lem517223 m)). Qed.
Lemma lem517230 : term81 = term82.
Proof. exact (fun_ext (fun m : nat => @lem517225 m)). Qed.
Lemma lem517231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517232 : term83 = term84.
Proof. exact (MK_COMB (@lem517231) (@lem517230)). Qed.
Lemma lem517237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517238 : term85 = term86.
Proof. exact (MK_COMB (@lem517237) (@lem517232)). Qed.
Lemma lem517252 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (EQ_MP (@lem516994 n) (@lem516993 n)). Qed.
Lemma lem517253 (m : nat) : (BIT1 m) = (term2 m).
Proof. exact (@lem517252 m). Qed.
Lemma lem517254 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517255 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem517254) (@lem517253 m)). Qed.
Lemma lem517257 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516991 n) (@lem516990 n)). Qed.
Lemma lem517258 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem517255 m) (@lem517257 n)). Qed.
Lemma lem517259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517260 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem517259) (@lem517258 m n)). Qed.
Lemma lem517261 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem517262 (m : nat) (n : nat) : ((term87 m n) = (Peano.lt m n)) = ((term88 m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem517260 m n) (@lem517261 m n)). Qed.
Lemma lem517265 (m : nat) : (term91 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem517262 m n)). Qed.
Lemma lem517266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517267 (m : nat) : (term93 m) = (term94 m).
Proof. exact (MK_COMB (@lem517266) (@lem517265 m)). Qed.
Lemma lem517272 : term95 = term96.
Proof. exact (fun_ext (fun m : nat => @lem517267 m)). Qed.
Lemma lem517273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517274 : term97 = term98.
Proof. exact (MK_COMB (@lem517273) (@lem517272)). Qed.
Lemma lem517279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem517280 : term99 = term100.
Proof. exact (MK_COMB (@lem517279) (@lem517274)). Qed.
Lemma lem517292 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (EQ_MP (@lem516994 n) (@lem516993 n)). Qed.
Lemma lem517293 (m : nat) : (BIT1 m) = (term2 m).
Proof. exact (@lem517292 m). Qed.
Lemma lem517294 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem517295 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem517294) (@lem517293 m)). Qed.
Lemma lem517297 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (EQ_MP (@lem516994 n) (@lem516993 n)). Qed.
Lemma lem517298 (m : nat) (n : nat) : (term101 m n) = (term102 m n).
Proof. exact (MK_COMB (@lem517295 m) (@lem517297 n)). Qed.
Lemma lem517299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem517300 (m : nat) (n : nat) : (term103 m n) = (term104 m n).
Proof. exact (MK_COMB (@lem517299) (@lem517298 m n)). Qed.
Lemma lem517301 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem517302 (m : nat) (n : nat) : ((term101 m n) = (Peano.le m n)) = ((term102 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem517300 m n) (@lem517301 m n)). Qed.
Lemma lem517305 (m : nat) : (term105 m) = (term106 m).
Proof. exact (fun_ext (fun n : nat => @lem517302 m n)). Qed.
Lemma lem517306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517307 (m : nat) : (term107 m) = (term108 m).
Proof. exact (MK_COMB (@lem517306) (@lem517305 m)). Qed.
Lemma lem517312 : term109 = term110.
Proof. exact (fun_ext (fun m : nat => @lem517307 m)). Qed.
Lemma lem517313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem517314 : term111 = term112.
Proof. exact (MK_COMB (@lem517313) (@lem517312)). Qed.
Lemma lem517319 : term113 = term114.
Proof. exact (MK_COMB (@lem517280) (@lem517314)). Qed.
Lemma lem517322 : term115 = term116.
Proof. exact (MK_COMB (@lem517238) (@lem517319)). Qed.
Lemma lem517325 : term117 = term118.
Proof. exact (MK_COMB (@lem517196) (@lem517322)). Qed.
Lemma lem517328 : term119 = term120.
Proof. exact (MK_COMB (@lem517154) (@lem517325)). Qed.
Lemma lem517331 : term121 = term122.
Proof. exact (MK_COMB (@lem517131) (@lem517328)). Qed.
Lemma lem517334 : term123 = term124.
Proof. exact (MK_COMB (@lem517108) (@lem517331)). Qed.
Lemma lem517337 : term125 = term126.
Proof. exact (MK_COMB (@lem517081) (@lem517334)). Qed.
Lemma lem517340 : term127 = term128.
Proof. exact (MK_COMB (@lem517052) (@lem517337)). Qed.
Lemma lem517343 : term129 = term130.
Proof. exact (MK_COMB (@lem517045) (@lem517340)). Qed.
Lemma lem517345 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem517346 : term130 = term128.
Proof. exact (@lem517345 term128). Qed.
Lemma lem517421 : term129 = term128.
Proof. exact (TRANS (@lem517343) (@lem517346)). Qed.
Lemma lem517422 : term128 = term129.
Proof. exact (SYM (@lem517421)). Qed.
