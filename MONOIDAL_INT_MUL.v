Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONOIDAL_INT_MUL_term_abbrevs.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982733_spec.
Require Import thm1982745_spec.
Require Import thm1982747_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2841544_spec.
Require Import thm2841579_spec.
Require Import thm2841580_spec.
Require Import thm2841585_spec.
Require Import thm2841586_spec.
Require Import thm2841591_spec.
Require Import thm2841592_spec.
Require Import thm2841615_spec.
Require Import thm2841616_spec.
Require Import thm2954598_spec.
Require Import thm6904637_spec.
Require Import thm6905935_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6905937 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem6905938 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem6905941 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem6905938 A op) (@lem6905937 A op)). Qed.
Lemma lem6905942 (op : type1551) : (@monoidal int op) = (term2 op).
Proof. exact (@lem6905941 int op). Qed.
Lemma lem6905943 : (@monoidal int int_mul) = term3.
Proof. exact (@lem6905942 int_mul). Qed.
Lemma lem6905979 : (@neutral int int_mul) = term4.
Proof. exact (EQ_MP (@lem6904637) (@lem6905935)). Qed.
Lemma lem6905980 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem6905981 : term5 = term6.
Proof. exact (MK_COMB (@lem6905980) (@lem6905979)). Qed.
Lemma lem6905982 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6905983 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem6905981) (@lem6905982 x)). Qed.
Lemma lem6905984 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6905985 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem6905984) (@lem6905983 x)). Qed.
Lemma lem6905986 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6905987 (x : int) : ((term7 x) = x) = ((term8 x) = x).
Proof. exact (MK_COMB (@lem6905985 x) (@lem6905986 x)). Qed.
Lemma lem6905990 : term11 = term12.
Proof. exact (fun_ext (fun x : int => @lem6905987 x)). Qed.
Lemma lem6905991 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6905992 : term13 = term14.
Proof. exact (MK_COMB (@lem6905991) (@lem6905990)). Qed.
Lemma lem6905997 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem6905998 : term16 = term17.
Proof. exact (MK_COMB (@lem6905997) (@lem6905992)). Qed.
Lemma lem6906001 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem6906002 : term3 = term19.
Proof. exact (MK_COMB (@lem6906001) (@lem6905998)). Qed.
Lemma lem6906005 : (@monoidal int int_mul) = term19.
Proof. exact (TRANS (@lem6905943) (@lem6906002)). Qed.
Lemma lem6906006 : term19 = (@monoidal int int_mul).
Proof. exact (SYM (@lem6906005)). Qed.
Lemma lem6906007 : term20 = term19.
Proof. exact (@lem2954598 term19). Qed.
Lemma lem6906042 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6906043 (x : int) : (term23 x) = (term24 x).
Proof. exact (@lem6906042 (term25 x)). Qed.
Lemma lem6906044 (y : int) (x : int) : (term26 x y) = ((int_mul x y) = (int_mul y x)).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem6906045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6906047 (y : int) (x : int) : (term27 x y) = (term28 y x).
Proof. exact (MK_COMB (@lem6906045) (@lem6906044 y x)). Qed.
Lemma lem6906048 (x : int) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : int => @lem6906047 y x)). Qed.
Lemma lem6906049 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906050 (x : int) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem6906049) (@lem6906048 x)). Qed.
Lemma lem6906051 (x : int) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem6906043 x) (@lem6906050 x)). Qed.
Lemma lem6906052 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6906053 : term32 = term33.
Proof. exact (@lem6906052 term34). Qed.
Lemma lem6906054 (x : int) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem6906055 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6906056 (x : int) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem6906055) (@lem6906054 x)). Qed.
Lemma lem6906057 (x : int) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem6906056 x) (@lem6906051 x)). Qed.
Lemma lem6906058 : term38 = term39.
Proof. exact (fun_ext (fun x : int => @lem6906057 x)). Qed.
Lemma lem6906059 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906060 : term33 = term40.
Proof. exact (MK_COMB (@lem6906059) (@lem6906058)). Qed.
Lemma lem6906061 : term32 = term40.
Proof. exact (TRANS (@lem6906053) (@lem6906060)). Qed.
Lemma lem6906063 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6906064 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (@lem6906063 (term43 x y)). Qed.
Lemma lem6906065 (x : int) (y : int) (z : int) : (term44 x y z) = ((term45 x y z) = (term46 x y z)).
Proof. exact (eq_refl (term44 x y z)). Qed.
Lemma lem6906066 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6906068 (x : int) (y : int) (z : int) : (term47 x y z) = (term48 x y z).
Proof. exact (MK_COMB (@lem6906066) (@lem6906065 x y z)). Qed.
Lemma lem6906069 (x : int) (y : int) : (term49 x y) = (term50 x y).
Proof. exact (fun_ext (fun z : int => @lem6906068 x y z)). Qed.
Lemma lem6906070 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906071 (x : int) (y : int) : (term42 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem6906070) (@lem6906069 x y)). Qed.
Lemma lem6906072 (x : int) (y : int) : (term41 x y) = (term51 x y).
Proof. exact (TRANS (@lem6906064 x y) (@lem6906071 x y)). Qed.
Lemma lem6906073 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6906074 (x : int) : (term52 x) = (term53 x).
Proof. exact (@lem6906073 (term54 x)). Qed.
Lemma lem6906075 (x : int) (y : int) : (term55 x y) = (term56 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem6906076 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6906077 (x : int) (y : int) : (term57 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem6906076) (@lem6906075 x y)). Qed.
Lemma lem6906078 (x : int) (y : int) : (term57 x y) = (term51 x y).
Proof. exact (TRANS (@lem6906077 x y) (@lem6906072 x y)). Qed.
Lemma lem6906079 (x : int) : (term58 x) = (term59 x).
Proof. exact (fun_ext (fun y : int => @lem6906078 x y)). Qed.
Lemma lem6906080 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906081 (x : int) : (term53 x) = (term60 x).
Proof. exact (MK_COMB (@lem6906080) (@lem6906079 x)). Qed.
Lemma lem6906082 (x : int) : (term52 x) = (term60 x).
Proof. exact (TRANS (@lem6906074 x) (@lem6906081 x)). Qed.
Lemma lem6906083 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6906084 : term61 = term62.
Proof. exact (@lem6906083 term63). Qed.
Lemma lem6906085 (x : int) : (term64 x) = (term65 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem6906086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6906087 (x : int) : (term66 x) = (term52 x).
Proof. exact (MK_COMB (@lem6906086) (@lem6906085 x)). Qed.
Lemma lem6906088 (x : int) : (term66 x) = (term60 x).
Proof. exact (TRANS (@lem6906087 x) (@lem6906082 x)). Qed.
Lemma lem6906089 : term67 = term68.
Proof. exact (fun_ext (fun x : int => @lem6906088 x)). Qed.
Lemma lem6906090 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906091 : term62 = term69.
Proof. exact (MK_COMB (@lem6906090) (@lem6906089)). Qed.
Lemma lem6906092 : term61 = term69.
Proof. exact (TRANS (@lem6906084) (@lem6906091)). Qed.
Lemma lem6906094 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6906095 : term70 = term71.
Proof. exact (@lem6906094 term12). Qed.
Lemma lem6906096 (x : int) : (term72 x) = ((term8 x) = x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem6906097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6906099 (x : int) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem6906097) (@lem6906096 x)). Qed.
Lemma lem6906100 : term75 = term76.
Proof. exact (fun_ext (fun x : int => @lem6906099 x)). Qed.
Lemma lem6906101 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906102 : term71 = term77.
Proof. exact (MK_COMB (@lem6906101) (@lem6906100)). Qed.
Lemma lem6906103 : term70 = term77.
Proof. exact (TRANS (@lem6906095) (@lem6906102)). Qed.
Lemma lem6906104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906105 : term78 = term79.
Proof. exact (MK_COMB (@lem6906104) (@lem6906092)). Qed.
Lemma lem6906106 : term80 = term81.
Proof. exact (MK_COMB (@lem6906105) (@lem6906103)). Qed.
Lemma lem6906107 : term82 = term80.
Proof. exact (@lem17045 term83 term14). Qed.
Lemma lem6906108 : term82 = term81.
Proof. exact (TRANS (@lem6906107) (@lem6906106)). Qed.
Lemma lem6906109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906110 : term84 = term85.
Proof. exact (MK_COMB (@lem6906109) (@lem6906061)). Qed.
Lemma lem6906111 : term86 = term87.
Proof. exact (MK_COMB (@lem6906110) (@lem6906108)). Qed.
Lemma lem6906112 : term88 = term86.
Proof. exact (@lem17045 term89 term17). Qed.
Lemma lem6906114 : term88 = term87.
Proof. exact (TRANS (@lem6906112) (@lem6906111)). Qed.
Lemma lem6906117 (y : int) (x : int) : (term28 y x) = (term28 y x).
Proof. exact (eq_refl (term28 y x)). Qed.
Lemma lem6906118 (x : int) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : int => @lem6906117 y x)). Qed.
Lemma lem6906119 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906120 (x : int) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem6906119) (@lem6906118 x)). Qed.
Lemma lem6906121 : term39 = term39.
Proof. exact (fun_ext (fun x : int => @lem6906120 x)). Qed.
Lemma lem6906122 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906123 : term40 = term40.
Proof. exact (MK_COMB (@lem6906122) (@lem6906121)). Qed.
Lemma lem6906126 (x : int) (y : int) (z : int) : (term48 x y z) = (term48 x y z).
Proof. exact (eq_refl (term48 x y z)). Qed.
Lemma lem6906127 (x : int) (y : int) : (term50 x y) = (term50 x y).
Proof. exact (fun_ext (fun z : int => @lem6906126 x y z)). Qed.
Lemma lem6906128 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906129 (x : int) (y : int) : (term51 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem6906128) (@lem6906127 x y)). Qed.
Lemma lem6906130 (x : int) : (term59 x) = (term59 x).
Proof. exact (fun_ext (fun y : int => @lem6906129 x y)). Qed.
Lemma lem6906131 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906132 (x : int) : (term60 x) = (term60 x).
Proof. exact (MK_COMB (@lem6906131) (@lem6906130 x)). Qed.
Lemma lem6906133 : term68 = term68.
Proof. exact (fun_ext (fun x : int => @lem6906132 x)). Qed.
Lemma lem6906134 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906135 : term69 = term69.
Proof. exact (MK_COMB (@lem6906134) (@lem6906133)). Qed.
Lemma lem6906138 (x : int) : (term74 x) = (term74 x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem6906139 : term76 = term76.
Proof. exact (fun_ext (fun x : int => @lem6906138 x)). Qed.
Lemma lem6906140 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906141 : term77 = term77.
Proof. exact (MK_COMB (@lem6906140) (@lem6906139)). Qed.
Lemma lem6906142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906143 : term79 = term79.
Proof. exact (MK_COMB (@lem6906142) (@lem6906135)). Qed.
Lemma lem6906144 : term81 = term81.
Proof. exact (MK_COMB (@lem6906143) (@lem6906141)). Qed.
Lemma lem6906145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906146 : term85 = term85.
Proof. exact (MK_COMB (@lem6906145) (@lem6906123)). Qed.
Lemma lem6906147 : term87 = term87.
Proof. exact (MK_COMB (@lem6906146) (@lem6906144)). Qed.
Lemma lem6906186 : term88 = term87.
Proof. exact (TRANS (@lem6906114) (@lem6906147)). Qed.
Lemma lem6906188 (y : int) (x : int) : (term90 x y) = (term91 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem6906189 (x : int) (y : int) : (term28 y x) = (term92 x y).
Proof. exact (@lem6906188 (int_mul y x) (int_mul x y)). Qed.
Lemma lem6906191 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6906192 (y : int) (x : int) : (term94 y x) = (term95 y x).
Proof. exact (@lem6906191 (term96 x y) (int_mul y x)). Qed.
Lemma lem6906194 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6906195 (x : int) (y : int) : (term99 x y) = (term100 x y).
Proof. exact (@lem6906194 (int_mul x y) term4). Qed.
Lemma lem6906197 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906198 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906199 (x : int) (y : int) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem6906198) (@lem6906197 x y)). Qed.
Lemma lem6906201 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906202 : term106 = term107.
Proof. exact (@lem6906201 term108). Qed.
Lemma lem6906203 (x : int) (y : int) : (term100 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem6906199 x y) (@lem6906202)). Qed.
Lemma lem6906204 (x : int) (y : int) : (term99 x y) = (term109 x y).
Proof. exact (TRANS (@lem6906195 x y) (@lem6906203 x y)). Qed.
Lemma lem6906205 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6906206 (x : int) (y : int) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem6906205) (@lem6906204 x y)). Qed.
Lemma lem6906208 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906209 (y : int) (x : int) : (term101 y x) = (term102 y x).
Proof. exact (@lem6906208 y x). Qed.
Lemma lem6906210 (y : int) (x : int) : (term95 y x) = (term112 y x).
Proof. exact (MK_COMB (@lem6906206 x y) (@lem6906209 y x)). Qed.
Lemma lem6906211 (y : int) (x : int) : (term94 y x) = (term112 y x).
Proof. exact (TRANS (@lem6906192 y x) (@lem6906210 y x)). Qed.
Lemma lem6906212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906213 (y : int) (x : int) : (term113 y x) = (term114 y x).
Proof. exact (MK_COMB (@lem6906212) (@lem6906211 y x)). Qed.
Lemma lem6906215 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6906216 (x : int) (y : int) : (term94 x y) = (term95 x y).
Proof. exact (@lem6906215 (term96 y x) (int_mul x y)). Qed.
Lemma lem6906218 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6906219 (y : int) (x : int) : (term99 y x) = (term100 y x).
Proof. exact (@lem6906218 (int_mul y x) term4). Qed.
Lemma lem6906221 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906222 (y : int) (x : int) : (term101 y x) = (term102 y x).
Proof. exact (@lem6906221 y x). Qed.
Lemma lem6906223 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906224 (y : int) (x : int) : (term103 y x) = (term104 y x).
Proof. exact (MK_COMB (@lem6906223) (@lem6906222 y x)). Qed.
Lemma lem6906226 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906227 : term106 = term107.
Proof. exact (@lem6906226 term108). Qed.
Lemma lem6906228 (y : int) (x : int) : (term100 y x) = (term109 y x).
Proof. exact (MK_COMB (@lem6906224 y x) (@lem6906227)). Qed.
Lemma lem6906229 (y : int) (x : int) : (term99 y x) = (term109 y x).
Proof. exact (TRANS (@lem6906219 y x) (@lem6906228 y x)). Qed.
Lemma lem6906230 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6906231 (y : int) (x : int) : (term110 y x) = (term111 y x).
Proof. exact (MK_COMB (@lem6906230) (@lem6906229 y x)). Qed.
Lemma lem6906233 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906234 (x : int) (y : int) : (term95 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem6906231 y x) (@lem6906233 x y)). Qed.
Lemma lem6906235 (x : int) (y : int) : (term94 x y) = (term112 x y).
Proof. exact (TRANS (@lem6906216 x y) (@lem6906234 x y)). Qed.
Lemma lem6906236 (x : int) (y : int) : (term92 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem6906213 y x) (@lem6906235 x y)). Qed.
Lemma lem6906237 (x : int) (y : int) : (term28 y x) = (term115 x y).
Proof. exact (TRANS (@lem6906189 x y) (@lem6906236 x y)). Qed.
Lemma lem6906238 (x : int) : (term30 x) = (term116 x).
Proof. exact (fun_ext (fun y : int => @lem6906237 x y)). Qed.
Lemma lem6906239 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906240 (x : int) : (term31 x) = (term117 x).
Proof. exact (MK_COMB (@lem6906239) (@lem6906238 x)). Qed.
Lemma lem6906241 : term39 = term118.
Proof. exact (fun_ext (fun x : int => @lem6906240 x)). Qed.
Lemma lem6906242 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906243 : term40 = term119.
Proof. exact (MK_COMB (@lem6906242) (@lem6906241)). Qed.
Lemma lem6906245 (y : int) (x : int) : (term90 x y) = (term91 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem6906246 (x : int) (y : int) (z : int) : (term48 x y z) = (term120 x y z).
Proof. exact (@lem6906245 (term46 x y z) (term45 x y z)). Qed.
Lemma lem6906248 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6906249 (x : int) (y : int) (z : int) : (term121 x y z) = (term122 x y z).
Proof. exact (@lem6906248 (term123 x y z) (term46 x y z)). Qed.
Lemma lem6906251 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6906252 (x : int) (y : int) (z : int) : (term124 x y z) = (term125 x y z).
Proof. exact (@lem6906251 (term45 x y z) term4). Qed.
Lemma lem6906254 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906255 (x : int) (y : int) (z : int) : (term126 x y z) = (term127 x y z).
Proof. exact (@lem6906254 x (int_mul y z)). Qed.
Lemma lem6906257 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906258 (y : int) (z : int) : (term101 y z) = (term102 y z).
Proof. exact (@lem6906257 y z). Qed.
Lemma lem6906259 (x : int) : (term128 x) = (term128 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem6906260 (x : int) (y : int) (z : int) : (term127 x y z) = (term129 x y z).
Proof. exact (MK_COMB (@lem6906259 x) (@lem6906258 y z)). Qed.
Lemma lem6906261 (x : int) (y : int) (z : int) : (term126 x y z) = (term129 x y z).
Proof. exact (TRANS (@lem6906255 x y z) (@lem6906260 x y z)). Qed.
Lemma lem6906262 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906263 (x : int) (y : int) (z : int) : (term130 x y z) = (term131 x y z).
Proof. exact (MK_COMB (@lem6906262) (@lem6906261 x y z)). Qed.
Lemma lem6906265 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906266 : term106 = term107.
Proof. exact (@lem6906265 term108). Qed.
Lemma lem6906267 (x : int) (y : int) (z : int) : (term125 x y z) = (term132 x y z).
Proof. exact (MK_COMB (@lem6906263 x y z) (@lem6906266)). Qed.
Lemma lem6906268 (x : int) (y : int) (z : int) : (term124 x y z) = (term132 x y z).
Proof. exact (TRANS (@lem6906252 x y z) (@lem6906267 x y z)). Qed.
Lemma lem6906269 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6906270 (x : int) (y : int) (z : int) : (term133 x y z) = (term134 x y z).
Proof. exact (MK_COMB (@lem6906269) (@lem6906268 x y z)). Qed.
Lemma lem6906272 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906273 (x : int) (y : int) (z : int) : (term135 x y z) = (term136 x y z).
Proof. exact (@lem6906272 (int_mul x y) z). Qed.
Lemma lem6906275 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6906277 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (MK_COMB (@lem6906276) (@lem6906275 x y)). Qed.
Lemma lem6906278 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem6906279 (x : int) (y : int) (z : int) : (term136 x y z) = (term139 x y z).
Proof. exact (MK_COMB (@lem6906277 x y) (@lem6906278 z)). Qed.
Lemma lem6906280 (x : int) (y : int) (z : int) : (term135 x y z) = (term139 x y z).
Proof. exact (TRANS (@lem6906273 x y z) (@lem6906279 x y z)). Qed.
Lemma lem6906281 (x : int) (y : int) (z : int) : (term122 x y z) = (term140 x y z).
Proof. exact (MK_COMB (@lem6906270 x y z) (@lem6906280 x y z)). Qed.
Lemma lem6906282 (x : int) (y : int) (z : int) : (term121 x y z) = (term140 x y z).
Proof. exact (TRANS (@lem6906249 x y z) (@lem6906281 x y z)). Qed.
Lemma lem6906283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906284 (x : int) (y : int) (z : int) : (term141 x y z) = (term142 x y z).
Proof. exact (MK_COMB (@lem6906283) (@lem6906282 x y z)). Qed.
Lemma lem6906286 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6906287 (x : int) (y : int) (z : int) : (term143 x y z) = (term144 x y z).
Proof. exact (@lem6906286 (term145 x y z) (term45 x y z)). Qed.
Lemma lem6906289 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6906290 (x : int) (y : int) (z : int) : (term146 x y z) = (term147 x y z).
Proof. exact (@lem6906289 (term46 x y z) term4). Qed.
Lemma lem6906292 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906293 (x : int) (y : int) (z : int) : (term135 x y z) = (term136 x y z).
Proof. exact (@lem6906292 (int_mul x y) z). Qed.
Lemma lem6906295 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6906297 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (MK_COMB (@lem6906296) (@lem6906295 x y)). Qed.
Lemma lem6906298 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem6906299 (x : int) (y : int) (z : int) : (term136 x y z) = (term139 x y z).
Proof. exact (MK_COMB (@lem6906297 x y) (@lem6906298 z)). Qed.
Lemma lem6906300 (x : int) (y : int) (z : int) : (term135 x y z) = (term139 x y z).
Proof. exact (TRANS (@lem6906293 x y z) (@lem6906299 x y z)). Qed.
Lemma lem6906301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906302 (x : int) (y : int) (z : int) : (term148 x y z) = (term149 x y z).
Proof. exact (MK_COMB (@lem6906301) (@lem6906300 x y z)). Qed.
Lemma lem6906304 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906305 : term106 = term107.
Proof. exact (@lem6906304 term108). Qed.
Lemma lem6906306 (x : int) (y : int) (z : int) : (term147 x y z) = (term150 x y z).
Proof. exact (MK_COMB (@lem6906302 x y z) (@lem6906305)). Qed.
Lemma lem6906307 (x : int) (y : int) (z : int) : (term146 x y z) = (term150 x y z).
Proof. exact (TRANS (@lem6906290 x y z) (@lem6906306 x y z)). Qed.
Lemma lem6906308 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6906309 (x : int) (y : int) (z : int) : (term151 x y z) = (term152 x y z).
Proof. exact (MK_COMB (@lem6906308) (@lem6906307 x y z)). Qed.
Lemma lem6906311 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906312 (x : int) (y : int) (z : int) : (term126 x y z) = (term127 x y z).
Proof. exact (@lem6906311 x (int_mul y z)). Qed.
Lemma lem6906314 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906315 (y : int) (z : int) : (term101 y z) = (term102 y z).
Proof. exact (@lem6906314 y z). Qed.
Lemma lem6906316 (x : int) : (term128 x) = (term128 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem6906317 (x : int) (y : int) (z : int) : (term127 x y z) = (term129 x y z).
Proof. exact (MK_COMB (@lem6906316 x) (@lem6906315 y z)). Qed.
Lemma lem6906318 (x : int) (y : int) (z : int) : (term126 x y z) = (term129 x y z).
Proof. exact (TRANS (@lem6906312 x y z) (@lem6906317 x y z)). Qed.
Lemma lem6906319 (x : int) (y : int) (z : int) : (term144 x y z) = (term153 x y z).
Proof. exact (MK_COMB (@lem6906309 x y z) (@lem6906318 x y z)). Qed.
Lemma lem6906320 (x : int) (y : int) (z : int) : (term143 x y z) = (term153 x y z).
Proof. exact (TRANS (@lem6906287 x y z) (@lem6906319 x y z)). Qed.
Lemma lem6906321 (x : int) (y : int) (z : int) : (term120 x y z) = (term154 x y z).
Proof. exact (MK_COMB (@lem6906284 x y z) (@lem6906320 x y z)). Qed.
Lemma lem6906322 (x : int) (y : int) (z : int) : (term48 x y z) = (term154 x y z).
Proof. exact (TRANS (@lem6906246 x y z) (@lem6906321 x y z)). Qed.
Lemma lem6906323 (x : int) (y : int) : (term50 x y) = (term155 x y).
Proof. exact (fun_ext (fun z : int => @lem6906322 x y z)). Qed.
Lemma lem6906324 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906325 (x : int) (y : int) : (term51 x y) = (term156 x y).
Proof. exact (MK_COMB (@lem6906324) (@lem6906323 x y)). Qed.
Lemma lem6906326 (x : int) : (term59 x) = (term157 x).
Proof. exact (fun_ext (fun y : int => @lem6906325 x y)). Qed.
Lemma lem6906327 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906328 (x : int) : (term60 x) = (term158 x).
Proof. exact (MK_COMB (@lem6906327) (@lem6906326 x)). Qed.
Lemma lem6906329 : term68 = term159.
Proof. exact (fun_ext (fun x : int => @lem6906328 x)). Qed.
Lemma lem6906330 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906331 : term69 = term160.
Proof. exact (MK_COMB (@lem6906330) (@lem6906329)). Qed.
Lemma lem6906333 (y : int) (x : int) : (term90 x y) = (term91 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem6906334 (x : int) : (term74 x) = (term161 x).
Proof. exact (@lem6906333 x (term8 x)). Qed.
Lemma lem6906336 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6906337 (x : int) : (term162 x) = (term163 x).
Proof. exact (@lem6906336 (term164 x) x). Qed.
Lemma lem6906339 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6906340 (x : int) : (term165 x) = (term166 x).
Proof. exact (@lem6906339 (term8 x) term4). Qed.
Lemma lem6906342 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906343 (x : int) : (term167 x) = (term168 x).
Proof. exact (@lem6906342 term4 x). Qed.
Lemma lem6906345 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906346 : term106 = term107.
Proof. exact (@lem6906345 term108). Qed.
Lemma lem6906347 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6906348 : term169 = term170.
Proof. exact (MK_COMB (@lem6906347) (@lem6906346)). Qed.
Lemma lem6906349 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6906350 (x : int) : (term168 x) = (term171 x).
Proof. exact (MK_COMB (@lem6906348) (@lem6906349 x)). Qed.
Lemma lem6906351 (x : int) : (term167 x) = (term171 x).
Proof. exact (TRANS (@lem6906343 x) (@lem6906350 x)). Qed.
Lemma lem6906352 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906353 (x : int) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem6906352) (@lem6906351 x)). Qed.
Lemma lem6906355 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906356 : term106 = term107.
Proof. exact (@lem6906355 term108). Qed.
Lemma lem6906357 (x : int) : (term166 x) = (term174 x).
Proof. exact (MK_COMB (@lem6906353 x) (@lem6906356)). Qed.
Lemma lem6906358 (x : int) : (term165 x) = (term174 x).
Proof. exact (TRANS (@lem6906340 x) (@lem6906357 x)). Qed.
Lemma lem6906359 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6906360 (x : int) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem6906359) (@lem6906358 x)). Qed.
Lemma lem6906361 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6906362 (x : int) : (term163 x) = (term177 x).
Proof. exact (MK_COMB (@lem6906360 x) (@lem6906361 x)). Qed.
Lemma lem6906363 (x : int) : (term162 x) = (term177 x).
Proof. exact (TRANS (@lem6906337 x) (@lem6906362 x)). Qed.
Lemma lem6906364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906365 (x : int) : (term178 x) = (term179 x).
Proof. exact (MK_COMB (@lem6906364) (@lem6906363 x)). Qed.
Lemma lem6906367 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6906368 (x : int) : (term180 x) = (term181 x).
Proof. exact (@lem6906367 (term182 x) (term8 x)). Qed.
Lemma lem6906370 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6906371 (x : int) : (term183 x) = (term184 x).
Proof. exact (@lem6906370 x term4). Qed.
Lemma lem6906373 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906374 : term106 = term107.
Proof. exact (@lem6906373 term108). Qed.
Lemma lem6906375 (x : int) : (term185 x) = (term185 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem6906376 (x : int) : (term184 x) = (term186 x).
Proof. exact (MK_COMB (@lem6906375 x) (@lem6906374)). Qed.
Lemma lem6906377 (x : int) : (term183 x) = (term186 x).
Proof. exact (TRANS (@lem6906371 x) (@lem6906376 x)). Qed.
Lemma lem6906378 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6906379 (x : int) : (term187 x) = (term188 x).
Proof. exact (MK_COMB (@lem6906378) (@lem6906377 x)). Qed.
Lemma lem6906381 (x : int) (y : int) : (term101 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem6906382 (x : int) : (term167 x) = (term168 x).
Proof. exact (@lem6906381 term4 x). Qed.
Lemma lem6906384 (n : nat) : (term105 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6906385 : term106 = term107.
Proof. exact (@lem6906384 term108). Qed.
Lemma lem6906386 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6906387 : term169 = term170.
Proof. exact (MK_COMB (@lem6906386) (@lem6906385)). Qed.
Lemma lem6906388 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6906389 (x : int) : (term168 x) = (term171 x).
Proof. exact (MK_COMB (@lem6906387) (@lem6906388 x)). Qed.
Lemma lem6906390 (x : int) : (term167 x) = (term171 x).
Proof. exact (TRANS (@lem6906382 x) (@lem6906389 x)). Qed.
Lemma lem6906391 (x : int) : (term181 x) = (term189 x).
Proof. exact (MK_COMB (@lem6906379 x) (@lem6906390 x)). Qed.
Lemma lem6906392 (x : int) : (term180 x) = (term189 x).
Proof. exact (TRANS (@lem6906368 x) (@lem6906391 x)). Qed.
Lemma lem6906393 (x : int) : (term161 x) = (term190 x).
Proof. exact (MK_COMB (@lem6906365 x) (@lem6906392 x)). Qed.
Lemma lem6906394 (x : int) : (term74 x) = (term190 x).
Proof. exact (TRANS (@lem6906334 x) (@lem6906393 x)). Qed.
Lemma lem6906395 : term76 = term191.
Proof. exact (fun_ext (fun x : int => @lem6906394 x)). Qed.
Lemma lem6906396 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906397 : term77 = term192.
Proof. exact (MK_COMB (@lem6906396) (@lem6906395)). Qed.
Lemma lem6906398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906399 : term79 = term193.
Proof. exact (MK_COMB (@lem6906398) (@lem6906331)). Qed.
Lemma lem6906400 : term81 = term194.
Proof. exact (MK_COMB (@lem6906399) (@lem6906397)). Qed.
Lemma lem6906401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906402 : term85 = term195.
Proof. exact (MK_COMB (@lem6906401) (@lem6906243)). Qed.
Lemma lem6906403 : term87 = term196.
Proof. exact (MK_COMB (@lem6906402) (@lem6906400)). Qed.
Lemma lem6906404 : term88 = term196.
Proof. exact (TRANS (@lem6906186) (@lem6906403)). Qed.
Lemma lem6906408 (t : Prop) : (term197 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6906409 : term198 = term196.
Proof. exact (@lem6906408 term196). Qed.
Lemma lem6906417 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6906418 (P : int -> Prop) (Q : int -> Prop) : (term201 P Q) = (term202 P Q).
Proof. exact (@lem6906417 int P Q). Qed.
Lemma lem6906419 (x : int) : (term203 x) = (term204 x).
Proof. exact (@lem6906418 (term205 x) (term206 x)). Qed.
Lemma lem6906420 (y : int) (x : int) : (term207 x y) = (term112 y x).
Proof. exact (eq_refl (term207 x y)). Qed.
Lemma lem6906421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906422 (y : int) (x : int) : (term208 x y) = (term114 y x).
Proof. exact (MK_COMB (@lem6906421) (@lem6906420 y x)). Qed.
Lemma lem6906423 (x : int) (y : int) : (term209 x y) = (term112 x y).
Proof. exact (eq_refl (term209 x y)). Qed.
Lemma lem6906424 (x : int) (y : int) : (term210 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem6906422 y x) (@lem6906423 x y)). Qed.
Lemma lem6906425 (x : int) : (term211 x) = (term116 x).
Proof. exact (fun_ext (fun y : int => @lem6906424 x y)). Qed.
Lemma lem6906426 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906427 (x : int) : (term203 x) = (term117 x).
Proof. exact (MK_COMB (@lem6906426) (@lem6906425 x)). Qed.
Lemma lem6906428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6906429 (x : int) : (term212 x) = (term213 x).
Proof. exact (MK_COMB (@lem6906428) (@lem6906427 x)). Qed.
Lemma lem6906430 (y : int) (x : int) : (term207 x y) = (term112 y x).
Proof. exact (eq_refl (term207 x y)). Qed.
Lemma lem6906431 (x : int) : (term214 x) = (term205 x).
Proof. exact (fun_ext (fun y : int => @lem6906430 y x)). Qed.
Lemma lem6906432 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906433 (x : int) : (term215 x) = (term216 x).
Proof. exact (MK_COMB (@lem6906432) (@lem6906431 x)). Qed.
Lemma lem6906434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906435 (x : int) : (term217 x) = (term218 x).
Proof. exact (MK_COMB (@lem6906434) (@lem6906433 x)). Qed.
Lemma lem6906436 (x : int) (y : int) : (term209 x y) = (term112 x y).
Proof. exact (eq_refl (term209 x y)). Qed.
Lemma lem6906437 (x : int) : (term219 x) = (term206 x).
Proof. exact (fun_ext (fun y : int => @lem6906436 x y)). Qed.
Lemma lem6906438 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906439 (x : int) : (term220 x) = (term221 x).
Proof. exact (MK_COMB (@lem6906438) (@lem6906437 x)). Qed.
Lemma lem6906440 (x : int) : (term204 x) = (term222 x).
Proof. exact (MK_COMB (@lem6906435 x) (@lem6906439 x)). Qed.
Lemma lem6906441 (x : int) : ((term203 x) = (term204 x)) = ((term117 x) = (term222 x)).
Proof. exact (MK_COMB (@lem6906429 x) (@lem6906440 x)). Qed.
Lemma lem6906442 (x : int) : (term117 x) = (term222 x).
Proof. exact (EQ_MP (@lem6906441 x) (@lem6906419 x)). Qed.
Lemma lem6906453 : term118 = term223.
Proof. exact (fun_ext (fun x : int => @lem6906442 x)). Qed.
Lemma lem6906454 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906455 : term119 = term224.
Proof. exact (MK_COMB (@lem6906454) (@lem6906453)). Qed.
Lemma lem6906457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6906458 (P : int -> Prop) (Q : int -> Prop) : (term201 P Q) = (term202 P Q).
Proof. exact (@lem6906457 int P Q). Qed.
Lemma lem6906459 : term225 = term226.
Proof. exact (@lem6906458 term227 term228). Qed.
Lemma lem6906460 (x : int) : (term229 x) = (term216 x).
Proof. exact (eq_refl (term229 x)). Qed.
Lemma lem6906461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906462 (x : int) : (term230 x) = (term218 x).
Proof. exact (MK_COMB (@lem6906461) (@lem6906460 x)). Qed.
Lemma lem6906463 (x : int) : (term231 x) = (term221 x).
Proof. exact (eq_refl (term231 x)). Qed.
Lemma lem6906464 (x : int) : (term232 x) = (term222 x).
Proof. exact (MK_COMB (@lem6906462 x) (@lem6906463 x)). Qed.
Lemma lem6906465 : term233 = term223.
Proof. exact (fun_ext (fun x : int => @lem6906464 x)). Qed.
Lemma lem6906466 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906467 : term225 = term224.
Proof. exact (MK_COMB (@lem6906466) (@lem6906465)). Qed.
Lemma lem6906468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6906469 : term234 = term235.
Proof. exact (MK_COMB (@lem6906468) (@lem6906467)). Qed.
Lemma lem6906470 (x : int) : (term229 x) = (term216 x).
Proof. exact (eq_refl (term229 x)). Qed.
Lemma lem6906471 : term236 = term227.
Proof. exact (fun_ext (fun x : int => @lem6906470 x)). Qed.
Lemma lem6906472 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906473 : term237 = term238.
Proof. exact (MK_COMB (@lem6906472) (@lem6906471)). Qed.
Lemma lem6906474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906475 : term239 = term240.
Proof. exact (MK_COMB (@lem6906474) (@lem6906473)). Qed.
Lemma lem6906476 (x : int) : (term231 x) = (term221 x).
Proof. exact (eq_refl (term231 x)). Qed.
Lemma lem6906477 : term241 = term228.
Proof. exact (fun_ext (fun x : int => @lem6906476 x)). Qed.
Lemma lem6906478 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906479 : term242 = term243.
Proof. exact (MK_COMB (@lem6906478) (@lem6906477)). Qed.
Lemma lem6906480 : term226 = term244.
Proof. exact (MK_COMB (@lem6906475) (@lem6906479)). Qed.
Lemma lem6906481 : (term225 = term226) = (term224 = term244).
Proof. exact (MK_COMB (@lem6906469) (@lem6906480)). Qed.
Lemma lem6906482 : term224 = term244.
Proof. exact (EQ_MP (@lem6906481) (@lem6906459)). Qed.
Lemma lem6906501 : term119 = term244.
Proof. exact (TRANS (@lem6906455) (@lem6906482)). Qed.
Lemma lem6906502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906503 : term195 = term245.
Proof. exact (MK_COMB (@lem6906502) (@lem6906501)). Qed.
Lemma lem6906515 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6906516 (P : int -> Prop) (Q : int -> Prop) : (term201 P Q) = (term202 P Q).
Proof. exact (@lem6906515 int P Q). Qed.
Lemma lem6906517 (x : int) (y : int) : (term246 x y) = (term247 x y).
Proof. exact (@lem6906516 (term248 x y) (term249 x y)). Qed.
Lemma lem6906518 (x : int) (y : int) (z : int) : (term250 x y z) = (term140 x y z).
Proof. exact (eq_refl (term250 x y z)). Qed.
Lemma lem6906519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906520 (x : int) (y : int) (z : int) : (term251 x y z) = (term142 x y z).
Proof. exact (MK_COMB (@lem6906519) (@lem6906518 x y z)). Qed.
Lemma lem6906521 (x : int) (y : int) (z : int) : (term252 x y z) = (term153 x y z).
Proof. exact (eq_refl (term252 x y z)). Qed.
Lemma lem6906522 (x : int) (y : int) (z : int) : (term253 x y z) = (term154 x y z).
Proof. exact (MK_COMB (@lem6906520 x y z) (@lem6906521 x y z)). Qed.
Lemma lem6906523 (x : int) (y : int) : (term254 x y) = (term155 x y).
Proof. exact (fun_ext (fun z : int => @lem6906522 x y z)). Qed.
Lemma lem6906524 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906525 (x : int) (y : int) : (term246 x y) = (term156 x y).
Proof. exact (MK_COMB (@lem6906524) (@lem6906523 x y)). Qed.
Lemma lem6906526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6906527 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem6906526) (@lem6906525 x y)). Qed.
Lemma lem6906528 (x : int) (y : int) (z : int) : (term250 x y z) = (term140 x y z).
Proof. exact (eq_refl (term250 x y z)). Qed.
Lemma lem6906529 (x : int) (y : int) : (term257 x y) = (term248 x y).
Proof. exact (fun_ext (fun z : int => @lem6906528 x y z)). Qed.
Lemma lem6906530 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906531 (x : int) (y : int) : (term258 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem6906530) (@lem6906529 x y)). Qed.
Lemma lem6906532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906533 (x : int) (y : int) : (term260 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem6906532) (@lem6906531 x y)). Qed.
Lemma lem6906534 (x : int) (y : int) (z : int) : (term252 x y z) = (term153 x y z).
Proof. exact (eq_refl (term252 x y z)). Qed.
Lemma lem6906535 (x : int) (y : int) : (term262 x y) = (term249 x y).
Proof. exact (fun_ext (fun z : int => @lem6906534 x y z)). Qed.
Lemma lem6906536 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906537 (x : int) (y : int) : (term263 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem6906536) (@lem6906535 x y)). Qed.
Lemma lem6906538 (x : int) (y : int) : (term247 x y) = (term265 x y).
Proof. exact (MK_COMB (@lem6906533 x y) (@lem6906537 x y)). Qed.
Lemma lem6906539 (x : int) (y : int) : ((term246 x y) = (term247 x y)) = ((term156 x y) = (term265 x y)).
Proof. exact (MK_COMB (@lem6906527 x y) (@lem6906538 x y)). Qed.
Lemma lem6906540 (x : int) (y : int) : (term156 x y) = (term265 x y).
Proof. exact (EQ_MP (@lem6906539 x y) (@lem6906517 x y)). Qed.
Lemma lem6906551 (x : int) : (term157 x) = (term266 x).
Proof. exact (fun_ext (fun y : int => @lem6906540 x y)). Qed.
Lemma lem6906552 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906553 (x : int) : (term158 x) = (term267 x).
Proof. exact (MK_COMB (@lem6906552) (@lem6906551 x)). Qed.
Lemma lem6906555 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6906556 (P : int -> Prop) (Q : int -> Prop) : (term201 P Q) = (term202 P Q).
Proof. exact (@lem6906555 int P Q). Qed.
Lemma lem6906557 (x : int) : (term268 x) = (term269 x).
Proof. exact (@lem6906556 (term270 x) (term271 x)). Qed.
Lemma lem6906558 (x : int) (y : int) : (term272 x y) = (term259 x y).
Proof. exact (eq_refl (term272 x y)). Qed.
Lemma lem6906559 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906560 (x : int) (y : int) : (term273 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem6906559) (@lem6906558 x y)). Qed.
Lemma lem6906561 (x : int) (y : int) : (term274 x y) = (term264 x y).
Proof. exact (eq_refl (term274 x y)). Qed.
Lemma lem6906562 (x : int) (y : int) : (term275 x y) = (term265 x y).
Proof. exact (MK_COMB (@lem6906560 x y) (@lem6906561 x y)). Qed.
Lemma lem6906563 (x : int) : (term276 x) = (term266 x).
Proof. exact (fun_ext (fun y : int => @lem6906562 x y)). Qed.
Lemma lem6906564 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906565 (x : int) : (term268 x) = (term267 x).
Proof. exact (MK_COMB (@lem6906564) (@lem6906563 x)). Qed.
Lemma lem6906566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6906567 (x : int) : (term277 x) = (term278 x).
Proof. exact (MK_COMB (@lem6906566) (@lem6906565 x)). Qed.
Lemma lem6906568 (x : int) (y : int) : (term272 x y) = (term259 x y).
Proof. exact (eq_refl (term272 x y)). Qed.
Lemma lem6906569 (x : int) : (term279 x) = (term270 x).
Proof. exact (fun_ext (fun y : int => @lem6906568 x y)). Qed.
Lemma lem6906570 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906571 (x : int) : (term280 x) = (term281 x).
Proof. exact (MK_COMB (@lem6906570) (@lem6906569 x)). Qed.
Lemma lem6906572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906573 (x : int) : (term282 x) = (term283 x).
Proof. exact (MK_COMB (@lem6906572) (@lem6906571 x)). Qed.
Lemma lem6906574 (x : int) (y : int) : (term274 x y) = (term264 x y).
Proof. exact (eq_refl (term274 x y)). Qed.
Lemma lem6906575 (x : int) : (term284 x) = (term271 x).
Proof. exact (fun_ext (fun y : int => @lem6906574 x y)). Qed.
Lemma lem6906576 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906577 (x : int) : (term285 x) = (term286 x).
Proof. exact (MK_COMB (@lem6906576) (@lem6906575 x)). Qed.
Lemma lem6906578 (x : int) : (term269 x) = (term287 x).
Proof. exact (MK_COMB (@lem6906573 x) (@lem6906577 x)). Qed.
Lemma lem6906579 (x : int) : ((term268 x) = (term269 x)) = ((term267 x) = (term287 x)).
Proof. exact (MK_COMB (@lem6906567 x) (@lem6906578 x)). Qed.
Lemma lem6906580 (x : int) : (term267 x) = (term287 x).
Proof. exact (EQ_MP (@lem6906579 x) (@lem6906557 x)). Qed.
Lemma lem6906599 (x : int) : (term158 x) = (term287 x).
Proof. exact (TRANS (@lem6906553 x) (@lem6906580 x)). Qed.
Lemma lem6906600 : term159 = term288.
Proof. exact (fun_ext (fun x : int => @lem6906599 x)). Qed.
Lemma lem6906601 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906602 : term160 = term289.
Proof. exact (MK_COMB (@lem6906601) (@lem6906600)). Qed.
Lemma lem6906604 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6906605 (P : int -> Prop) (Q : int -> Prop) : (term201 P Q) = (term202 P Q).
Proof. exact (@lem6906604 int P Q). Qed.
Lemma lem6906606 : term290 = term291.
Proof. exact (@lem6906605 term292 term293). Qed.
Lemma lem6906607 (x : int) : (term294 x) = (term281 x).
Proof. exact (eq_refl (term294 x)). Qed.
Lemma lem6906608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906609 (x : int) : (term295 x) = (term283 x).
Proof. exact (MK_COMB (@lem6906608) (@lem6906607 x)). Qed.
Lemma lem6906610 (x : int) : (term296 x) = (term286 x).
Proof. exact (eq_refl (term296 x)). Qed.
Lemma lem6906611 (x : int) : (term297 x) = (term287 x).
Proof. exact (MK_COMB (@lem6906609 x) (@lem6906610 x)). Qed.
Lemma lem6906612 : term298 = term288.
Proof. exact (fun_ext (fun x : int => @lem6906611 x)). Qed.
Lemma lem6906613 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906614 : term290 = term289.
Proof. exact (MK_COMB (@lem6906613) (@lem6906612)). Qed.
Lemma lem6906615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6906616 : term299 = term300.
Proof. exact (MK_COMB (@lem6906615) (@lem6906614)). Qed.
Lemma lem6906617 (x : int) : (term294 x) = (term281 x).
Proof. exact (eq_refl (term294 x)). Qed.
Lemma lem6906618 : term301 = term292.
Proof. exact (fun_ext (fun x : int => @lem6906617 x)). Qed.
Lemma lem6906619 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906620 : term302 = term303.
Proof. exact (MK_COMB (@lem6906619) (@lem6906618)). Qed.
Lemma lem6906621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906622 : term304 = term305.
Proof. exact (MK_COMB (@lem6906621) (@lem6906620)). Qed.
Lemma lem6906623 (x : int) : (term296 x) = (term286 x).
Proof. exact (eq_refl (term296 x)). Qed.
Lemma lem6906624 : term306 = term293.
Proof. exact (fun_ext (fun x : int => @lem6906623 x)). Qed.
Lemma lem6906625 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906626 : term307 = term308.
Proof. exact (MK_COMB (@lem6906625) (@lem6906624)). Qed.
Lemma lem6906627 : term291 = term309.
Proof. exact (MK_COMB (@lem6906622) (@lem6906626)). Qed.
Lemma lem6906628 : (term290 = term291) = (term289 = term309).
Proof. exact (MK_COMB (@lem6906616) (@lem6906627)). Qed.
Lemma lem6906629 : term289 = term309.
Proof. exact (EQ_MP (@lem6906628) (@lem6906606)). Qed.
Lemma lem6906656 : term160 = term309.
Proof. exact (TRANS (@lem6906602) (@lem6906629)). Qed.
Lemma lem6906657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906658 : term193 = term310.
Proof. exact (MK_COMB (@lem6906657) (@lem6906656)). Qed.
Lemma lem6906660 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6906661 (P : int -> Prop) (Q : int -> Prop) : (term201 P Q) = (term202 P Q).
Proof. exact (@lem6906660 int P Q). Qed.
Lemma lem6906662 : term311 = term312.
Proof. exact (@lem6906661 term313 term314). Qed.
Lemma lem6906663 (x : int) : (term315 x) = (term177 x).
Proof. exact (eq_refl (term315 x)). Qed.
Lemma lem6906664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906665 (x : int) : (term316 x) = (term179 x).
Proof. exact (MK_COMB (@lem6906664) (@lem6906663 x)). Qed.
Lemma lem6906666 (x : int) : (term317 x) = (term189 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem6906667 (x : int) : (term318 x) = (term190 x).
Proof. exact (MK_COMB (@lem6906665 x) (@lem6906666 x)). Qed.
Lemma lem6906668 : term319 = term191.
Proof. exact (fun_ext (fun x : int => @lem6906667 x)). Qed.
Lemma lem6906669 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906670 : term311 = term192.
Proof. exact (MK_COMB (@lem6906669) (@lem6906668)). Qed.
Lemma lem6906671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6906672 : term320 = term321.
Proof. exact (MK_COMB (@lem6906671) (@lem6906670)). Qed.
Lemma lem6906673 (x : int) : (term315 x) = (term177 x).
Proof. exact (eq_refl (term315 x)). Qed.
Lemma lem6906674 : term322 = term313.
Proof. exact (fun_ext (fun x : int => @lem6906673 x)). Qed.
Lemma lem6906675 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906676 : term323 = term324.
Proof. exact (MK_COMB (@lem6906675) (@lem6906674)). Qed.
Lemma lem6906677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906678 : term325 = term326.
Proof. exact (MK_COMB (@lem6906677) (@lem6906676)). Qed.
Lemma lem6906679 (x : int) : (term317 x) = (term189 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem6906680 : term327 = term314.
Proof. exact (fun_ext (fun x : int => @lem6906679 x)). Qed.
Lemma lem6906681 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906682 : term328 = term329.
Proof. exact (MK_COMB (@lem6906681) (@lem6906680)). Qed.
Lemma lem6906683 : term312 = term330.
Proof. exact (MK_COMB (@lem6906678) (@lem6906682)). Qed.
Lemma lem6906684 : (term311 = term312) = (term192 = term330).
Proof. exact (MK_COMB (@lem6906672) (@lem6906683)). Qed.
Lemma lem6906685 : term192 = term330.
Proof. exact (EQ_MP (@lem6906684) (@lem6906662)). Qed.
Lemma lem6906696 : term194 = term331.
Proof. exact (MK_COMB (@lem6906658) (@lem6906685)). Qed.
Lemma lem6906699 : term196 = term332.
Proof. exact (MK_COMB (@lem6906503) (@lem6906696)). Qed.
Lemma lem6906703 : term198 = term332.
Proof. exact (TRANS (@lem6906409) (@lem6906699)). Qed.
Lemma lem6906704 (y : int) (x : int) : (term112 y x) = (term112 y x).
Proof. exact (eq_refl (term112 y x)). Qed.
Lemma lem6906705 (x : int) : (term205 x) = (term205 x).
Proof. exact (fun_ext (fun y : int => @lem6906704 y x)). Qed.
Lemma lem6906706 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906707 (x : int) : (term216 x) = (term216 x).
Proof. exact (MK_COMB (@lem6906706) (@lem6906705 x)). Qed.
Lemma lem6906708 : term227 = term227.
Proof. exact (fun_ext (fun x : int => @lem6906707 x)). Qed.
Lemma lem6906709 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906710 : term238 = term238.
Proof. exact (MK_COMB (@lem6906709) (@lem6906708)). Qed.
Lemma lem6906711 (x : int) (y : int) : (term112 x y) = (term112 x y).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem6906712 (x : int) : (term206 x) = (term206 x).
Proof. exact (fun_ext (fun y : int => @lem6906711 x y)). Qed.
Lemma lem6906713 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906714 (x : int) : (term221 x) = (term221 x).
Proof. exact (MK_COMB (@lem6906713) (@lem6906712 x)). Qed.
Lemma lem6906715 : term228 = term228.
Proof. exact (fun_ext (fun x : int => @lem6906714 x)). Qed.
Lemma lem6906716 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906717 : term243 = term243.
Proof. exact (MK_COMB (@lem6906716) (@lem6906715)). Qed.
Lemma lem6906718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906719 : term240 = term240.
Proof. exact (MK_COMB (@lem6906718) (@lem6906710)). Qed.
Lemma lem6906720 : term244 = term244.
Proof. exact (MK_COMB (@lem6906719) (@lem6906717)). Qed.
Lemma lem6906721 (x : int) (y : int) (z : int) : (term140 x y z) = (term140 x y z).
Proof. exact (eq_refl (term140 x y z)). Qed.
Lemma lem6906722 (x : int) (y : int) : (term248 x y) = (term248 x y).
Proof. exact (fun_ext (fun z : int => @lem6906721 x y z)). Qed.
Lemma lem6906723 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906724 (x : int) (y : int) : (term259 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem6906723) (@lem6906722 x y)). Qed.
Lemma lem6906725 (x : int) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : int => @lem6906724 x y)). Qed.
Lemma lem6906726 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906727 (x : int) : (term281 x) = (term281 x).
Proof. exact (MK_COMB (@lem6906726) (@lem6906725 x)). Qed.
Lemma lem6906728 : term292 = term292.
Proof. exact (fun_ext (fun x : int => @lem6906727 x)). Qed.
Lemma lem6906729 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906730 : term303 = term303.
Proof. exact (MK_COMB (@lem6906729) (@lem6906728)). Qed.
Lemma lem6906731 (x : int) (y : int) (z : int) : (term153 x y z) = (term153 x y z).
Proof. exact (eq_refl (term153 x y z)). Qed.
Lemma lem6906732 (x : int) (y : int) : (term249 x y) = (term249 x y).
Proof. exact (fun_ext (fun z : int => @lem6906731 x y z)). Qed.
Lemma lem6906733 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906734 (x : int) (y : int) : (term264 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem6906733) (@lem6906732 x y)). Qed.
Lemma lem6906735 (x : int) : (term271 x) = (term271 x).
Proof. exact (fun_ext (fun y : int => @lem6906734 x y)). Qed.
Lemma lem6906736 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906737 (x : int) : (term286 x) = (term286 x).
Proof. exact (MK_COMB (@lem6906736) (@lem6906735 x)). Qed.
Lemma lem6906738 : term293 = term293.
Proof. exact (fun_ext (fun x : int => @lem6906737 x)). Qed.
Lemma lem6906739 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906740 : term308 = term308.
Proof. exact (MK_COMB (@lem6906739) (@lem6906738)). Qed.
Lemma lem6906741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906742 : term305 = term305.
Proof. exact (MK_COMB (@lem6906741) (@lem6906730)). Qed.
Lemma lem6906743 : term309 = term309.
Proof. exact (MK_COMB (@lem6906742) (@lem6906740)). Qed.
Lemma lem6906744 (x : int) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem6906745 : term313 = term313.
Proof. exact (fun_ext (fun x : int => @lem6906744 x)). Qed.
Lemma lem6906746 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906747 : term324 = term324.
Proof. exact (MK_COMB (@lem6906746) (@lem6906745)). Qed.
Lemma lem6906748 (x : int) : (term189 x) = (term189 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem6906749 : term314 = term314.
Proof. exact (fun_ext (fun x : int => @lem6906748 x)). Qed.
Lemma lem6906750 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906751 : term329 = term329.
Proof. exact (MK_COMB (@lem6906750) (@lem6906749)). Qed.
Lemma lem6906752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906753 : term326 = term326.
Proof. exact (MK_COMB (@lem6906752) (@lem6906747)). Qed.
Lemma lem6906754 : term330 = term330.
Proof. exact (MK_COMB (@lem6906753) (@lem6906751)). Qed.
Lemma lem6906755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906756 : term310 = term310.
Proof. exact (MK_COMB (@lem6906755) (@lem6906743)). Qed.
Lemma lem6906757 : term331 = term331.
Proof. exact (MK_COMB (@lem6906756) (@lem6906754)). Qed.
Lemma lem6906758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906759 : term245 = term245.
Proof. exact (MK_COMB (@lem6906758) (@lem6906720)). Qed.
Lemma lem6906760 : term332 = term332.
Proof. exact (MK_COMB (@lem6906759) (@lem6906757)). Qed.
Lemma lem6906761 : term198 = term332.
Proof. exact (TRANS (@lem6906703) (@lem6906760)). Qed.
Lemma lem6906762 (y : int) (x : int) : (term112 y x) = (term112 y x).
Proof. exact (eq_refl (term112 y x)). Qed.
Lemma lem6906763 (x : int) : (term205 x) = (term205 x).
Proof. exact (fun_ext (fun y : int => @lem6906762 y x)). Qed.
Lemma lem6906764 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906765 (x : int) : (term216 x) = (term216 x).
Proof. exact (MK_COMB (@lem6906764) (@lem6906763 x)). Qed.
Lemma lem6906766 : term227 = term227.
Proof. exact (fun_ext (fun x : int => @lem6906765 x)). Qed.
Lemma lem6906767 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906768 : term238 = term238.
Proof. exact (MK_COMB (@lem6906767) (@lem6906766)). Qed.
Lemma lem6906769 (x : int) (y : int) : (term112 x y) = (term112 x y).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem6906770 (x : int) : (term206 x) = (term206 x).
Proof. exact (fun_ext (fun y : int => @lem6906769 x y)). Qed.
Lemma lem6906771 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906772 (x : int) : (term221 x) = (term221 x).
Proof. exact (MK_COMB (@lem6906771) (@lem6906770 x)). Qed.
Lemma lem6906773 : term228 = term228.
Proof. exact (fun_ext (fun x : int => @lem6906772 x)). Qed.
Lemma lem6906774 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906775 : term243 = term243.
Proof. exact (MK_COMB (@lem6906774) (@lem6906773)). Qed.
Lemma lem6906776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906777 : term240 = term240.
Proof. exact (MK_COMB (@lem6906776) (@lem6906768)). Qed.
Lemma lem6906778 : term244 = term244.
Proof. exact (MK_COMB (@lem6906777) (@lem6906775)). Qed.
Lemma lem6906779 (x : int) (y : int) (z : int) : (term140 x y z) = (term140 x y z).
Proof. exact (eq_refl (term140 x y z)). Qed.
Lemma lem6906780 (x : int) (y : int) : (term248 x y) = (term248 x y).
Proof. exact (fun_ext (fun z : int => @lem6906779 x y z)). Qed.
Lemma lem6906781 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906782 (x : int) (y : int) : (term259 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem6906781) (@lem6906780 x y)). Qed.
Lemma lem6906783 (x : int) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : int => @lem6906782 x y)). Qed.
Lemma lem6906784 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906785 (x : int) : (term281 x) = (term281 x).
Proof. exact (MK_COMB (@lem6906784) (@lem6906783 x)). Qed.
Lemma lem6906786 : term292 = term292.
Proof. exact (fun_ext (fun x : int => @lem6906785 x)). Qed.
Lemma lem6906787 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906788 : term303 = term303.
Proof. exact (MK_COMB (@lem6906787) (@lem6906786)). Qed.
Lemma lem6906789 (x : int) (y : int) (z : int) : (term153 x y z) = (term153 x y z).
Proof. exact (eq_refl (term153 x y z)). Qed.
Lemma lem6906790 (x : int) (y : int) : (term249 x y) = (term249 x y).
Proof. exact (fun_ext (fun z : int => @lem6906789 x y z)). Qed.
Lemma lem6906791 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906792 (x : int) (y : int) : (term264 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem6906791) (@lem6906790 x y)). Qed.
Lemma lem6906793 (x : int) : (term271 x) = (term271 x).
Proof. exact (fun_ext (fun y : int => @lem6906792 x y)). Qed.
Lemma lem6906794 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906795 (x : int) : (term286 x) = (term286 x).
Proof. exact (MK_COMB (@lem6906794) (@lem6906793 x)). Qed.
Lemma lem6906796 : term293 = term293.
Proof. exact (fun_ext (fun x : int => @lem6906795 x)). Qed.
Lemma lem6906797 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906798 : term308 = term308.
Proof. exact (MK_COMB (@lem6906797) (@lem6906796)). Qed.
Lemma lem6906799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906800 : term305 = term305.
Proof. exact (MK_COMB (@lem6906799) (@lem6906788)). Qed.
Lemma lem6906801 : term309 = term309.
Proof. exact (MK_COMB (@lem6906800) (@lem6906798)). Qed.
Lemma lem6906802 (x : int) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem6906803 : term313 = term313.
Proof. exact (fun_ext (fun x : int => @lem6906802 x)). Qed.
Lemma lem6906804 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906805 : term324 = term324.
Proof. exact (MK_COMB (@lem6906804) (@lem6906803)). Qed.
Lemma lem6906806 (x : int) : (term189 x) = (term189 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem6906807 : term314 = term314.
Proof. exact (fun_ext (fun x : int => @lem6906806 x)). Qed.
Lemma lem6906808 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6906809 : term329 = term329.
Proof. exact (MK_COMB (@lem6906808) (@lem6906807)). Qed.
Lemma lem6906810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906811 : term326 = term326.
Proof. exact (MK_COMB (@lem6906810) (@lem6906805)). Qed.
Lemma lem6906812 : term330 = term330.
Proof. exact (MK_COMB (@lem6906811) (@lem6906809)). Qed.
Lemma lem6906813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906814 : term310 = term310.
Proof. exact (MK_COMB (@lem6906813) (@lem6906801)). Qed.
Lemma lem6906815 : term331 = term331.
Proof. exact (MK_COMB (@lem6906814) (@lem6906812)). Qed.
Lemma lem6906816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6906817 : term245 = term245.
Proof. exact (MK_COMB (@lem6906816) (@lem6906778)). Qed.
Lemma lem6906818 : term332 = term332.
Proof. exact (MK_COMB (@lem6906817) (@lem6906815)). Qed.
Lemma lem6906819 : term198 = term332.
Proof. exact (TRANS (@lem6906761) (@lem6906818)). Qed.
Lemma lem6906820 (x : int) (y : int) : (term112 y x) = (term333 x y).
Proof. exact (@lem1988287 (term102 y x) (term109 x y)). Qed.
Lemma lem6906833 (x : int) (y : int) : (term109 x y) = (term109 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem6906840 (x : int) (y : int) : (term102 y x) = (term102 x y).
Proof. exact (@lem1982747 (real_of_int x) (real_of_int y)). Qed.
Lemma lem6906841 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6906842 (x : int) (y : int) : (term334 y x) = (term334 x y).
Proof. exact (MK_COMB (@lem6906841) (@lem6906840 x y)). Qed.
Lemma lem6906843 (x : int) (y : int) : (term335 x y) = (term336 x y).
Proof. exact (MK_COMB (@lem6906842 x y) (@lem6906833 x y)). Qed.
Lemma lem6906844 (x : int) (y : int) : (term336 x y) = (term337 x y).
Proof. exact (@lem1982792 (term102 x y) (term109 x y)). Qed.
Lemma lem6906845 (x : int) (y : int) : (term338 x y) = (term339 x y).
Proof. exact (@lem1982781 (term102 x y) term340 term107). Qed.
Lemma lem6906847 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6906848 : term107 = term342.
Proof. exact (@lem6906847 term108). Qed.
Lemma lem6906850 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6906851 : term340 = term345.
Proof. exact (@lem6906850 term108). Qed.
Lemma lem6906852 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6906853 : term346 = term347.
Proof. exact (MK_COMB (@lem6906852) (@lem6906851)). Qed.
Lemma lem6906854 : term348 = term349.
Proof. exact (MK_COMB (@lem6906853) (@lem6906848)). Qed.
Lemma lem6906855 : term349 = term350.
Proof. exact (@lem1981613 term340 term107 term107 term107). Qed.
Lemma lem6906857 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6906858 : term353 = term354.
Proof. exact (@lem6906857 term108 term108). Qed.
Lemma lem6906859 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6906860 : term356 = term108.
Proof. exact (EQ_MP (@lem6906859) (@lem940073)). Qed.
Lemma lem6906861 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6906862 : term354 = term107.
Proof. exact (MK_COMB (@lem6906861) (@lem6906860)). Qed.
Lemma lem6906863 : term353 = term107.
Proof. exact (TRANS (@lem6906858) (@lem6906862)). Qed.
Lemma lem6906865 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6906866 : term348 = term359.
Proof. exact (@lem6906865 term108 term108). Qed.
Lemma lem6906867 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6906868 : term356 = term108.
Proof. exact (EQ_MP (@lem6906867) (@lem940073)). Qed.
Lemma lem6906869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6906870 : term354 = term107.
Proof. exact (MK_COMB (@lem6906869) (@lem6906868)). Qed.
Lemma lem6906871 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6906872 : term359 = term340.
Proof. exact (MK_COMB (@lem6906871) (@lem6906870)). Qed.
Lemma lem6906873 : term348 = term340.
Proof. exact (TRANS (@lem6906866) (@lem6906872)). Qed.
Lemma lem6906874 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6906875 : term360 = term361.
Proof. exact (MK_COMB (@lem6906874) (@lem6906873)). Qed.
Lemma lem6906876 : term350 = term345.
Proof. exact (MK_COMB (@lem6906875) (@lem6906863)). Qed.
Lemma lem6906877 : term349 = term345.
Proof. exact (TRANS (@lem6906855) (@lem6906876)). Qed.
Lemma lem6906878 : term348 = term345.
Proof. exact (TRANS (@lem6906854) (@lem6906877)). Qed.
Lemma lem6906880 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6906881 : term345 = term340.
Proof. exact (@lem6906880 term340). Qed.
Lemma lem6906882 : term348 = term340.
Proof. exact (TRANS (@lem6906878) (@lem6906881)). Qed.
Lemma lem6906885 (x : int) (y : int) : (term363 x y) = (term363 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem6906886 (x : int) (y : int) : (term339 x y) = (term364 x y).
Proof. exact (MK_COMB (@lem6906885 x y) (@lem6906882)). Qed.
Lemma lem6906887 (x : int) (y : int) : (term338 x y) = (term364 x y).
Proof. exact (TRANS (@lem6906845 x y) (@lem6906886 x y)). Qed.
Lemma lem6906888 (x : int) (y : int) : (term104 x y) = (term104 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem6906889 (x : int) (y : int) : (term337 x y) = (term365 x y).
Proof. exact (MK_COMB (@lem6906888 x y) (@lem6906887 x y)). Qed.
Lemma lem6906890 (x : int) (y : int) : (term365 x y) = (term366 x y).
Proof. exact (@lem1982763 (term102 x y) (term367 x y) term340). Qed.
Lemma lem6906891 (x : int) (y : int) : (term368 x y) = (term369 x y).
Proof. exact (@lem1982715 term340 (term102 x y)). Qed.
Lemma lem6906893 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6906894 : term107 = term342.
Proof. exact (@lem6906893 term108). Qed.
Lemma lem6906896 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6906897 : term340 = term345.
Proof. exact (@lem6906896 term108). Qed.
Lemma lem6906898 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906899 : term370 = term371.
Proof. exact (MK_COMB (@lem6906898) (@lem6906897)). Qed.
Lemma lem6906900 : term372 = term373.
Proof. exact (MK_COMB (@lem6906899) (@lem6906894)). Qed.
Lemma lem6906901 : term374.
Proof. exact (@lem1981473 term340 term107 term107 term107 term375 term107). Qed.
Lemma lem6906903 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6906904 : term377 = term378.
Proof. exact (@lem6906903 (NUMERAL 0) term108). Qed.
Lemma lem6906905 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6906906 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6906907 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6906906 h1) (fun h1 : term378 = True => @lem6906905)). Qed.
Lemma lem6906908 : term378 = True.
Proof. exact (EQ_MP (@lem6906907) (@lem6906905)). Qed.
Lemma lem6906909 : term377 = True.
Proof. exact (TRANS (@lem6906904) (@lem6906908)). Qed.
Lemma lem6906910 : True = term377.
Proof. exact (SYM (@lem6906909)). Qed.
Lemma lem6906911 : term377.
Proof. exact (EQ_MP (@lem6906910) (@lem0)). Qed.
Lemma lem6906912 : term380.
Proof. exact (@lem6906901 (@lem6906911)). Qed.
Lemma lem6906914 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6906915 : term377 = term378.
Proof. exact (@lem6906914 (NUMERAL 0) term108). Qed.
Lemma lem6906916 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6906917 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6906918 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6906917 h1) (fun h1 : term378 = True => @lem6906916)). Qed.
Lemma lem6906919 : term378 = True.
Proof. exact (EQ_MP (@lem6906918) (@lem6906916)). Qed.
Lemma lem6906920 : term377 = True.
Proof. exact (TRANS (@lem6906915) (@lem6906919)). Qed.
Lemma lem6906921 : True = term377.
Proof. exact (SYM (@lem6906920)). Qed.
Lemma lem6906922 : term377.
Proof. exact (EQ_MP (@lem6906921) (@lem0)). Qed.
Lemma lem6906923 : term381.
Proof. exact (@lem6906912 (@lem6906922)). Qed.
Lemma lem6906925 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6906926 : term377 = term378.
Proof. exact (@lem6906925 (NUMERAL 0) term108). Qed.
Lemma lem6906927 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6906928 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6906929 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6906928 h1) (fun h1 : term378 = True => @lem6906927)). Qed.
Lemma lem6906930 : term378 = True.
Proof. exact (EQ_MP (@lem6906929) (@lem6906927)). Qed.
Lemma lem6906931 : term377 = True.
Proof. exact (TRANS (@lem6906926) (@lem6906930)). Qed.
Lemma lem6906932 : True = term377.
Proof. exact (SYM (@lem6906931)). Qed.
Lemma lem6906933 : term377.
Proof. exact (EQ_MP (@lem6906932) (@lem0)). Qed.
Lemma lem6906934 : term382.
Proof. exact (@lem6906923 (@lem6906933)). Qed.
Lemma lem6906936 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6906937 : term353 = term354.
Proof. exact (@lem6906936 term108 term108). Qed.
Lemma lem6906938 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6906939 : term356 = term108.
Proof. exact (EQ_MP (@lem6906938) (@lem940073)). Qed.
Lemma lem6906940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6906941 : term354 = term107.
Proof. exact (MK_COMB (@lem6906940) (@lem6906939)). Qed.
Lemma lem6906942 : term353 = term107.
Proof. exact (TRANS (@lem6906937) (@lem6906941)). Qed.
Lemma lem6906944 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6906945 : term348 = term359.
Proof. exact (@lem6906944 term108 term108). Qed.
Lemma lem6906946 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6906947 : term356 = term108.
Proof. exact (EQ_MP (@lem6906946) (@lem940073)). Qed.
Lemma lem6906948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6906949 : term354 = term107.
Proof. exact (MK_COMB (@lem6906948) (@lem6906947)). Qed.
Lemma lem6906950 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6906951 : term359 = term340.
Proof. exact (MK_COMB (@lem6906950) (@lem6906949)). Qed.
Lemma lem6906952 : term348 = term340.
Proof. exact (TRANS (@lem6906945) (@lem6906951)). Qed.
Lemma lem6906953 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906954 : term383 = term370.
Proof. exact (MK_COMB (@lem6906953) (@lem6906952)). Qed.
Lemma lem6906955 : term384 = term372.
Proof. exact (MK_COMB (@lem6906954) (@lem6906942)). Qed.
Lemma lem6906957 (m : nat) : (term385 m) = term375.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6906958 : term372 = term375.
Proof. exact (@lem6906957 term108). Qed.
Lemma lem6906959 : term384 = term375.
Proof. exact (TRANS (@lem6906955) (@lem6906958)). Qed.
Lemma lem6906960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6906961 : term386 = term387.
Proof. exact (MK_COMB (@lem6906960) (@lem6906959)). Qed.
Lemma lem6906962 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6906963 : term388 = term389.
Proof. exact (MK_COMB (@lem6906961) (@lem6906962)). Qed.
Lemma lem6906965 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6906966 : term389 = term375.
Proof. exact (@lem6906965 term108). Qed.
Lemma lem6906967 : term388 = term375.
Proof. exact (TRANS (@lem6906963) (@lem6906966)). Qed.
Lemma lem6906969 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6906970 : term353 = term354.
Proof. exact (@lem6906969 term108 term108). Qed.
Lemma lem6906971 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6906972 : term356 = term108.
Proof. exact (EQ_MP (@lem6906971) (@lem940073)). Qed.
Lemma lem6906973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6906974 : term354 = term107.
Proof. exact (MK_COMB (@lem6906973) (@lem6906972)). Qed.
Lemma lem6906975 : term353 = term107.
Proof. exact (TRANS (@lem6906970) (@lem6906974)). Qed.
Lemma lem6906976 : term387 = term387.
Proof. exact (eq_refl term387). Qed.
Lemma lem6906977 : term391 = term389.
Proof. exact (MK_COMB (@lem6906976) (@lem6906975)). Qed.
Lemma lem6906979 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6906980 : term389 = term375.
Proof. exact (@lem6906979 term108). Qed.
Lemma lem6906981 : term391 = term375.
Proof. exact (TRANS (@lem6906977) (@lem6906980)). Qed.
Lemma lem6906982 : term375 = term391.
Proof. exact (SYM (@lem6906981)). Qed.
Lemma lem6906983 : term388 = term391.
Proof. exact (TRANS (@lem6906967) (@lem6906982)). Qed.
Lemma lem6906984 : term373 = term392.
Proof. exact (@lem6906934 (@lem6906983)). Qed.
Lemma lem6906985 : term372 = term392.
Proof. exact (TRANS (@lem6906900) (@lem6906984)). Qed.
Lemma lem6906987 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6906988 : term392 = term375.
Proof. exact (@lem6906987 term375). Qed.
Lemma lem6906989 : term372 = term375.
Proof. exact (TRANS (@lem6906985) (@lem6906988)). Qed.
Lemma lem6906990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6906991 : term393 = term387.
Proof. exact (MK_COMB (@lem6906990) (@lem6906989)). Qed.
Lemma lem6906992 (x : int) (y : int) : (term102 x y) = (term102 x y).
Proof. exact (eq_refl (term102 x y)). Qed.
Lemma lem6906993 (x : int) (y : int) : (term369 x y) = (term394 x y).
Proof. exact (MK_COMB (@lem6906991) (@lem6906992 x y)). Qed.
Lemma lem6906994 (x : int) (y : int) : (term368 x y) = (term394 x y).
Proof. exact (TRANS (@lem6906891 x y) (@lem6906993 x y)). Qed.
Lemma lem6906995 (x : int) (y : int) : (term394 x y) = term375.
Proof. exact (@lem1982719 (term102 x y)). Qed.
Lemma lem6906996 (x : int) (y : int) : (term368 x y) = term375.
Proof. exact (TRANS (@lem6906994 x y) (@lem6906995 x y)). Qed.
Lemma lem6906997 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6906998 (x : int) (y : int) : (term395 x y) = term396.
Proof. exact (MK_COMB (@lem6906997) (@lem6906996 x y)). Qed.
Lemma lem6906999 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem6907000 (x : int) (y : int) : (term366 x y) = term397.
Proof. exact (MK_COMB (@lem6906998 x y) (@lem6906999)). Qed.
Lemma lem6907001 (x : int) (y : int) : (term365 x y) = term397.
Proof. exact (TRANS (@lem6906890 x y) (@lem6907000 x y)). Qed.
Lemma lem6907002 : term397 = term340.
Proof. exact (@lem1982721 term340). Qed.
Lemma lem6907003 (x : int) (y : int) : (term365 x y) = term340.
Proof. exact (TRANS (@lem6907001 x y) (@lem6907002)). Qed.
Lemma lem6907004 (x : int) (y : int) : (term337 x y) = term340.
Proof. exact (TRANS (@lem6906889 x y) (@lem6907003 x y)). Qed.
Lemma lem6907005 (x : int) (y : int) : (term336 x y) = term340.
Proof. exact (TRANS (@lem6906844 x y) (@lem6907004 x y)). Qed.
Lemma lem6907006 (x : int) (y : int) : (term335 x y) = term340.
Proof. exact (TRANS (@lem6906843 x y) (@lem6907005 x y)). Qed.
Lemma lem6907007 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6907008 (x : int) (y : int) : (term398 x y) = term399.
Proof. exact (MK_COMB (@lem6907007) (@lem6907006 x y)). Qed.
Lemma lem6907009 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem6907010 (x : int) (y : int) : (term333 x y) = term400.
Proof. exact (MK_COMB (@lem6907008 x y) (@lem6907009)). Qed.
Lemma lem6907011 (y : int) (x : int) : (term112 y x) = term400.
Proof. exact (TRANS (@lem6906820 x y) (@lem6907010 x y)). Qed.
Lemma lem6907012 (x : int) : (term205 x) = term401.
Proof. exact (fun_ext (fun y : int => @lem6907011 y x)). Qed.
Lemma lem6907013 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907014 (x : int) : (term216 x) = term402.
Proof. exact (MK_COMB (@lem6907013) (@lem6907012 x)). Qed.
Lemma lem6907015 : term227 = term403.
Proof. exact (fun_ext (fun x : int => @lem6907014 x)). Qed.
Lemma lem6907016 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907017 : term238 = term404.
Proof. exact (MK_COMB (@lem6907016) (@lem6907015)). Qed.
Lemma lem6907018 (y : int) (x : int) : (term112 x y) = (term333 y x).
Proof. exact (@lem1988287 (term102 x y) (term109 y x)). Qed.
Lemma lem6907019 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907026 (x : int) (y : int) : (term102 y x) = (term102 x y).
Proof. exact (@lem1982747 (real_of_int x) (real_of_int y)). Qed.
Lemma lem6907027 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907028 (x : int) (y : int) : (term104 y x) = (term104 x y).
Proof. exact (MK_COMB (@lem6907027) (@lem6907026 x y)). Qed.
Lemma lem6907031 (x : int) (y : int) : (term109 y x) = (term109 x y).
Proof. exact (MK_COMB (@lem6907028 x y) (@lem6907019)). Qed.
Lemma lem6907040 (x : int) (y : int) : (term334 x y) = (term334 x y).
Proof. exact (eq_refl (term334 x y)). Qed.
Lemma lem6907041 (x : int) (y : int) : (term335 y x) = (term336 x y).
Proof. exact (MK_COMB (@lem6907040 x y) (@lem6907031 x y)). Qed.
Lemma lem6907042 (x : int) (y : int) : (term336 x y) = (term337 x y).
Proof. exact (@lem1982792 (term102 x y) (term109 x y)). Qed.
Lemma lem6907043 (x : int) (y : int) : (term338 x y) = (term339 x y).
Proof. exact (@lem1982781 (term102 x y) term340 term107). Qed.
Lemma lem6907045 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907046 : term107 = term342.
Proof. exact (@lem6907045 term108). Qed.
Lemma lem6907048 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907049 : term340 = term345.
Proof. exact (@lem6907048 term108). Qed.
Lemma lem6907050 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907051 : term346 = term347.
Proof. exact (MK_COMB (@lem6907050) (@lem6907049)). Qed.
Lemma lem6907052 : term348 = term349.
Proof. exact (MK_COMB (@lem6907051) (@lem6907046)). Qed.
Lemma lem6907053 : term349 = term350.
Proof. exact (@lem1981613 term340 term107 term107 term107). Qed.
Lemma lem6907055 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907056 : term353 = term354.
Proof. exact (@lem6907055 term108 term108). Qed.
Lemma lem6907057 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907058 : term356 = term108.
Proof. exact (EQ_MP (@lem6907057) (@lem940073)). Qed.
Lemma lem6907059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907060 : term354 = term107.
Proof. exact (MK_COMB (@lem6907059) (@lem6907058)). Qed.
Lemma lem6907061 : term353 = term107.
Proof. exact (TRANS (@lem6907056) (@lem6907060)). Qed.
Lemma lem6907063 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907064 : term348 = term359.
Proof. exact (@lem6907063 term108 term108). Qed.
Lemma lem6907065 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907066 : term356 = term108.
Proof. exact (EQ_MP (@lem6907065) (@lem940073)). Qed.
Lemma lem6907067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907068 : term354 = term107.
Proof. exact (MK_COMB (@lem6907067) (@lem6907066)). Qed.
Lemma lem6907069 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907070 : term359 = term340.
Proof. exact (MK_COMB (@lem6907069) (@lem6907068)). Qed.
Lemma lem6907071 : term348 = term340.
Proof. exact (TRANS (@lem6907064) (@lem6907070)). Qed.
Lemma lem6907072 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6907073 : term360 = term361.
Proof. exact (MK_COMB (@lem6907072) (@lem6907071)). Qed.
Lemma lem6907074 : term350 = term345.
Proof. exact (MK_COMB (@lem6907073) (@lem6907061)). Qed.
Lemma lem6907075 : term349 = term345.
Proof. exact (TRANS (@lem6907053) (@lem6907074)). Qed.
Lemma lem6907076 : term348 = term345.
Proof. exact (TRANS (@lem6907052) (@lem6907075)). Qed.
Lemma lem6907078 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6907079 : term345 = term340.
Proof. exact (@lem6907078 term340). Qed.
Lemma lem6907080 : term348 = term340.
Proof. exact (TRANS (@lem6907076) (@lem6907079)). Qed.
Lemma lem6907083 (x : int) (y : int) : (term363 x y) = (term363 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem6907084 (x : int) (y : int) : (term339 x y) = (term364 x y).
Proof. exact (MK_COMB (@lem6907083 x y) (@lem6907080)). Qed.
Lemma lem6907085 (x : int) (y : int) : (term338 x y) = (term364 x y).
Proof. exact (TRANS (@lem6907043 x y) (@lem6907084 x y)). Qed.
Lemma lem6907086 (x : int) (y : int) : (term104 x y) = (term104 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem6907087 (x : int) (y : int) : (term337 x y) = (term365 x y).
Proof. exact (MK_COMB (@lem6907086 x y) (@lem6907085 x y)). Qed.
Lemma lem6907088 (x : int) (y : int) : (term365 x y) = (term366 x y).
Proof. exact (@lem1982763 (term102 x y) (term367 x y) term340). Qed.
Lemma lem6907089 (x : int) (y : int) : (term368 x y) = (term369 x y).
Proof. exact (@lem1982715 term340 (term102 x y)). Qed.
Lemma lem6907091 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907092 : term107 = term342.
Proof. exact (@lem6907091 term108). Qed.
Lemma lem6907094 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907095 : term340 = term345.
Proof. exact (@lem6907094 term108). Qed.
Lemma lem6907096 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907097 : term370 = term371.
Proof. exact (MK_COMB (@lem6907096) (@lem6907095)). Qed.
Lemma lem6907098 : term372 = term373.
Proof. exact (MK_COMB (@lem6907097) (@lem6907092)). Qed.
Lemma lem6907099 : term374.
Proof. exact (@lem1981473 term340 term107 term107 term107 term375 term107). Qed.
Lemma lem6907101 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907102 : term377 = term378.
Proof. exact (@lem6907101 (NUMERAL 0) term108). Qed.
Lemma lem6907103 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907104 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907105 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907104 h1) (fun h1 : term378 = True => @lem6907103)). Qed.
Lemma lem6907106 : term378 = True.
Proof. exact (EQ_MP (@lem6907105) (@lem6907103)). Qed.
Lemma lem6907107 : term377 = True.
Proof. exact (TRANS (@lem6907102) (@lem6907106)). Qed.
Lemma lem6907108 : True = term377.
Proof. exact (SYM (@lem6907107)). Qed.
Lemma lem6907109 : term377.
Proof. exact (EQ_MP (@lem6907108) (@lem0)). Qed.
Lemma lem6907110 : term380.
Proof. exact (@lem6907099 (@lem6907109)). Qed.
Lemma lem6907112 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907113 : term377 = term378.
Proof. exact (@lem6907112 (NUMERAL 0) term108). Qed.
Lemma lem6907114 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907115 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907116 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907115 h1) (fun h1 : term378 = True => @lem6907114)). Qed.
Lemma lem6907117 : term378 = True.
Proof. exact (EQ_MP (@lem6907116) (@lem6907114)). Qed.
Lemma lem6907118 : term377 = True.
Proof. exact (TRANS (@lem6907113) (@lem6907117)). Qed.
Lemma lem6907119 : True = term377.
Proof. exact (SYM (@lem6907118)). Qed.
Lemma lem6907120 : term377.
Proof. exact (EQ_MP (@lem6907119) (@lem0)). Qed.
Lemma lem6907121 : term381.
Proof. exact (@lem6907110 (@lem6907120)). Qed.
Lemma lem6907123 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907124 : term377 = term378.
Proof. exact (@lem6907123 (NUMERAL 0) term108). Qed.
Lemma lem6907125 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907126 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907127 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907126 h1) (fun h1 : term378 = True => @lem6907125)). Qed.
Lemma lem6907128 : term378 = True.
Proof. exact (EQ_MP (@lem6907127) (@lem6907125)). Qed.
Lemma lem6907129 : term377 = True.
Proof. exact (TRANS (@lem6907124) (@lem6907128)). Qed.
Lemma lem6907130 : True = term377.
Proof. exact (SYM (@lem6907129)). Qed.
Lemma lem6907131 : term377.
Proof. exact (EQ_MP (@lem6907130) (@lem0)). Qed.
Lemma lem6907132 : term382.
Proof. exact (@lem6907121 (@lem6907131)). Qed.
Lemma lem6907134 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907135 : term353 = term354.
Proof. exact (@lem6907134 term108 term108). Qed.
Lemma lem6907136 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907137 : term356 = term108.
Proof. exact (EQ_MP (@lem6907136) (@lem940073)). Qed.
Lemma lem6907138 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907139 : term354 = term107.
Proof. exact (MK_COMB (@lem6907138) (@lem6907137)). Qed.
Lemma lem6907140 : term353 = term107.
Proof. exact (TRANS (@lem6907135) (@lem6907139)). Qed.
Lemma lem6907142 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907143 : term348 = term359.
Proof. exact (@lem6907142 term108 term108). Qed.
Lemma lem6907144 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907145 : term356 = term108.
Proof. exact (EQ_MP (@lem6907144) (@lem940073)). Qed.
Lemma lem6907146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907147 : term354 = term107.
Proof. exact (MK_COMB (@lem6907146) (@lem6907145)). Qed.
Lemma lem6907148 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907149 : term359 = term340.
Proof. exact (MK_COMB (@lem6907148) (@lem6907147)). Qed.
Lemma lem6907150 : term348 = term340.
Proof. exact (TRANS (@lem6907143) (@lem6907149)). Qed.
Lemma lem6907151 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907152 : term383 = term370.
Proof. exact (MK_COMB (@lem6907151) (@lem6907150)). Qed.
Lemma lem6907153 : term384 = term372.
Proof. exact (MK_COMB (@lem6907152) (@lem6907140)). Qed.
Lemma lem6907155 (m : nat) : (term385 m) = term375.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6907156 : term372 = term375.
Proof. exact (@lem6907155 term108). Qed.
Lemma lem6907157 : term384 = term375.
Proof. exact (TRANS (@lem6907153) (@lem6907156)). Qed.
Lemma lem6907158 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907159 : term386 = term387.
Proof. exact (MK_COMB (@lem6907158) (@lem6907157)). Qed.
Lemma lem6907160 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907161 : term388 = term389.
Proof. exact (MK_COMB (@lem6907159) (@lem6907160)). Qed.
Lemma lem6907163 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907164 : term389 = term375.
Proof. exact (@lem6907163 term108). Qed.
Lemma lem6907165 : term388 = term375.
Proof. exact (TRANS (@lem6907161) (@lem6907164)). Qed.
Lemma lem6907167 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907168 : term353 = term354.
Proof. exact (@lem6907167 term108 term108). Qed.
Lemma lem6907169 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907170 : term356 = term108.
Proof. exact (EQ_MP (@lem6907169) (@lem940073)). Qed.
Lemma lem6907171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907172 : term354 = term107.
Proof. exact (MK_COMB (@lem6907171) (@lem6907170)). Qed.
Lemma lem6907173 : term353 = term107.
Proof. exact (TRANS (@lem6907168) (@lem6907172)). Qed.
Lemma lem6907174 : term387 = term387.
Proof. exact (eq_refl term387). Qed.
Lemma lem6907175 : term391 = term389.
Proof. exact (MK_COMB (@lem6907174) (@lem6907173)). Qed.
Lemma lem6907177 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907178 : term389 = term375.
Proof. exact (@lem6907177 term108). Qed.
Lemma lem6907179 : term391 = term375.
Proof. exact (TRANS (@lem6907175) (@lem6907178)). Qed.
Lemma lem6907180 : term375 = term391.
Proof. exact (SYM (@lem6907179)). Qed.
Lemma lem6907181 : term388 = term391.
Proof. exact (TRANS (@lem6907165) (@lem6907180)). Qed.
Lemma lem6907182 : term373 = term392.
Proof. exact (@lem6907132 (@lem6907181)). Qed.
Lemma lem6907183 : term372 = term392.
Proof. exact (TRANS (@lem6907098) (@lem6907182)). Qed.
Lemma lem6907185 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6907186 : term392 = term375.
Proof. exact (@lem6907185 term375). Qed.
Lemma lem6907187 : term372 = term375.
Proof. exact (TRANS (@lem6907183) (@lem6907186)). Qed.
Lemma lem6907188 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907189 : term393 = term387.
Proof. exact (MK_COMB (@lem6907188) (@lem6907187)). Qed.
Lemma lem6907190 (x : int) (y : int) : (term102 x y) = (term102 x y).
Proof. exact (eq_refl (term102 x y)). Qed.
Lemma lem6907191 (x : int) (y : int) : (term369 x y) = (term394 x y).
Proof. exact (MK_COMB (@lem6907189) (@lem6907190 x y)). Qed.
Lemma lem6907192 (x : int) (y : int) : (term368 x y) = (term394 x y).
Proof. exact (TRANS (@lem6907089 x y) (@lem6907191 x y)). Qed.
Lemma lem6907193 (x : int) (y : int) : (term394 x y) = term375.
Proof. exact (@lem1982719 (term102 x y)). Qed.
Lemma lem6907194 (x : int) (y : int) : (term368 x y) = term375.
Proof. exact (TRANS (@lem6907192 x y) (@lem6907193 x y)). Qed.
Lemma lem6907195 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907196 (x : int) (y : int) : (term395 x y) = term396.
Proof. exact (MK_COMB (@lem6907195) (@lem6907194 x y)). Qed.
Lemma lem6907197 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem6907198 (x : int) (y : int) : (term366 x y) = term397.
Proof. exact (MK_COMB (@lem6907196 x y) (@lem6907197)). Qed.
Lemma lem6907199 (x : int) (y : int) : (term365 x y) = term397.
Proof. exact (TRANS (@lem6907088 x y) (@lem6907198 x y)). Qed.
Lemma lem6907200 : term397 = term340.
Proof. exact (@lem1982721 term340). Qed.
Lemma lem6907201 (x : int) (y : int) : (term365 x y) = term340.
Proof. exact (TRANS (@lem6907199 x y) (@lem6907200)). Qed.
Lemma lem6907202 (x : int) (y : int) : (term337 x y) = term340.
Proof. exact (TRANS (@lem6907087 x y) (@lem6907201 x y)). Qed.
Lemma lem6907203 (x : int) (y : int) : (term336 x y) = term340.
Proof. exact (TRANS (@lem6907042 x y) (@lem6907202 x y)). Qed.
Lemma lem6907204 (y : int) (x : int) : (term335 y x) = term340.
Proof. exact (TRANS (@lem6907041 x y) (@lem6907203 x y)). Qed.
Lemma lem6907205 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6907206 (y : int) (x : int) : (term398 y x) = term399.
Proof. exact (MK_COMB (@lem6907205) (@lem6907204 y x)). Qed.
Lemma lem6907207 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem6907208 (y : int) (x : int) : (term333 y x) = term400.
Proof. exact (MK_COMB (@lem6907206 y x) (@lem6907207)). Qed.
Lemma lem6907209 (x : int) (y : int) : (term112 x y) = term400.
Proof. exact (TRANS (@lem6907018 y x) (@lem6907208 y x)). Qed.
Lemma lem6907210 (x : int) : (term206 x) = term401.
Proof. exact (fun_ext (fun y : int => @lem6907209 x y)). Qed.
Lemma lem6907211 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907212 (x : int) : (term221 x) = term402.
Proof. exact (MK_COMB (@lem6907211) (@lem6907210 x)). Qed.
Lemma lem6907213 : term228 = term403.
Proof. exact (fun_ext (fun x : int => @lem6907212 x)). Qed.
Lemma lem6907214 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907215 : term243 = term404.
Proof. exact (MK_COMB (@lem6907214) (@lem6907213)). Qed.
Lemma lem6907216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6907217 : term240 = term405.
Proof. exact (MK_COMB (@lem6907216) (@lem6907017)). Qed.
Lemma lem6907218 : term244 = term406.
Proof. exact (MK_COMB (@lem6907217) (@lem6907215)). Qed.
Lemma lem6907219 (x : int) (y : int) (z : int) : (term140 x y z) = (term407 x y z).
Proof. exact (@lem1988287 (term139 x y z) (term132 x y z)). Qed.
Lemma lem6907238 (x : int) (y : int) (z : int) : (term132 x y z) = (term132 x y z).
Proof. exact (eq_refl (term132 x y z)). Qed.
Lemma lem6907255 (x : int) (y : int) (z : int) : (term139 x y z) = (term129 x y z).
Proof. exact (@lem1982745 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem6907256 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6907257 (x : int) (y : int) (z : int) : (term408 x y z) = (term409 x y z).
Proof. exact (MK_COMB (@lem6907256) (@lem6907255 x y z)). Qed.
Lemma lem6907258 (x : int) (y : int) (z : int) : (term410 x y z) = (term411 x y z).
Proof. exact (MK_COMB (@lem6907257 x y z) (@lem6907238 x y z)). Qed.
Lemma lem6907259 (x : int) (y : int) (z : int) : (term411 x y z) = (term412 x y z).
Proof. exact (@lem1982792 (term129 x y z) (term132 x y z)). Qed.
Lemma lem6907260 (x : int) (y : int) (z : int) : (term413 x y z) = (term414 x y z).
Proof. exact (@lem1982781 (term129 x y z) term340 term107). Qed.
Lemma lem6907262 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907263 : term107 = term342.
Proof. exact (@lem6907262 term108). Qed.
Lemma lem6907265 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907266 : term340 = term345.
Proof. exact (@lem6907265 term108). Qed.
Lemma lem6907267 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907268 : term346 = term347.
Proof. exact (MK_COMB (@lem6907267) (@lem6907266)). Qed.
Lemma lem6907269 : term348 = term349.
Proof. exact (MK_COMB (@lem6907268) (@lem6907263)). Qed.
Lemma lem6907270 : term349 = term350.
Proof. exact (@lem1981613 term340 term107 term107 term107). Qed.
Lemma lem6907272 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907273 : term353 = term354.
Proof. exact (@lem6907272 term108 term108). Qed.
Lemma lem6907274 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907275 : term356 = term108.
Proof. exact (EQ_MP (@lem6907274) (@lem940073)). Qed.
Lemma lem6907276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907277 : term354 = term107.
Proof. exact (MK_COMB (@lem6907276) (@lem6907275)). Qed.
Lemma lem6907278 : term353 = term107.
Proof. exact (TRANS (@lem6907273) (@lem6907277)). Qed.
Lemma lem6907280 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907281 : term348 = term359.
Proof. exact (@lem6907280 term108 term108). Qed.
Lemma lem6907282 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907283 : term356 = term108.
Proof. exact (EQ_MP (@lem6907282) (@lem940073)). Qed.
Lemma lem6907284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907285 : term354 = term107.
Proof. exact (MK_COMB (@lem6907284) (@lem6907283)). Qed.
Lemma lem6907286 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907287 : term359 = term340.
Proof. exact (MK_COMB (@lem6907286) (@lem6907285)). Qed.
Lemma lem6907288 : term348 = term340.
Proof. exact (TRANS (@lem6907281) (@lem6907287)). Qed.
Lemma lem6907289 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6907290 : term360 = term361.
Proof. exact (MK_COMB (@lem6907289) (@lem6907288)). Qed.
Lemma lem6907291 : term350 = term345.
Proof. exact (MK_COMB (@lem6907290) (@lem6907278)). Qed.
Lemma lem6907292 : term349 = term345.
Proof. exact (TRANS (@lem6907270) (@lem6907291)). Qed.
Lemma lem6907293 : term348 = term345.
Proof. exact (TRANS (@lem6907269) (@lem6907292)). Qed.
Lemma lem6907295 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6907296 : term345 = term340.
Proof. exact (@lem6907295 term340). Qed.
Lemma lem6907297 : term348 = term340.
Proof. exact (TRANS (@lem6907293) (@lem6907296)). Qed.
Lemma lem6907300 (x : int) (y : int) (z : int) : (term415 x y z) = (term415 x y z).
Proof. exact (eq_refl (term415 x y z)). Qed.
Lemma lem6907301 (x : int) (y : int) (z : int) : (term414 x y z) = (term416 x y z).
Proof. exact (MK_COMB (@lem6907300 x y z) (@lem6907297)). Qed.
Lemma lem6907302 (x : int) (y : int) (z : int) : (term413 x y z) = (term416 x y z).
Proof. exact (TRANS (@lem6907260 x y z) (@lem6907301 x y z)). Qed.
Lemma lem6907303 (x : int) (y : int) (z : int) : (term131 x y z) = (term131 x y z).
Proof. exact (eq_refl (term131 x y z)). Qed.
Lemma lem6907304 (x : int) (y : int) (z : int) : (term412 x y z) = (term417 x y z).
Proof. exact (MK_COMB (@lem6907303 x y z) (@lem6907302 x y z)). Qed.
Lemma lem6907305 (x : int) (y : int) (z : int) : (term417 x y z) = (term418 x y z).
Proof. exact (@lem1982763 (term129 x y z) (term419 x y z) term340). Qed.
Lemma lem6907306 (x : int) (y : int) (z : int) : (term420 x y z) = (term421 x y z).
Proof. exact (@lem1982715 term340 (term129 x y z)). Qed.
Lemma lem6907308 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907309 : term107 = term342.
Proof. exact (@lem6907308 term108). Qed.
Lemma lem6907311 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907312 : term340 = term345.
Proof. exact (@lem6907311 term108). Qed.
Lemma lem6907313 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907314 : term370 = term371.
Proof. exact (MK_COMB (@lem6907313) (@lem6907312)). Qed.
Lemma lem6907315 : term372 = term373.
Proof. exact (MK_COMB (@lem6907314) (@lem6907309)). Qed.
Lemma lem6907316 : term374.
Proof. exact (@lem1981473 term340 term107 term107 term107 term375 term107). Qed.
Lemma lem6907318 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907319 : term377 = term378.
Proof. exact (@lem6907318 (NUMERAL 0) term108). Qed.
Lemma lem6907320 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907321 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907322 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907321 h1) (fun h1 : term378 = True => @lem6907320)). Qed.
Lemma lem6907323 : term378 = True.
Proof. exact (EQ_MP (@lem6907322) (@lem6907320)). Qed.
Lemma lem6907324 : term377 = True.
Proof. exact (TRANS (@lem6907319) (@lem6907323)). Qed.
Lemma lem6907325 : True = term377.
Proof. exact (SYM (@lem6907324)). Qed.
Lemma lem6907326 : term377.
Proof. exact (EQ_MP (@lem6907325) (@lem0)). Qed.
Lemma lem6907327 : term380.
Proof. exact (@lem6907316 (@lem6907326)). Qed.
Lemma lem6907329 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907330 : term377 = term378.
Proof. exact (@lem6907329 (NUMERAL 0) term108). Qed.
Lemma lem6907331 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907332 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907333 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907332 h1) (fun h1 : term378 = True => @lem6907331)). Qed.
Lemma lem6907334 : term378 = True.
Proof. exact (EQ_MP (@lem6907333) (@lem6907331)). Qed.
Lemma lem6907335 : term377 = True.
Proof. exact (TRANS (@lem6907330) (@lem6907334)). Qed.
Lemma lem6907336 : True = term377.
Proof. exact (SYM (@lem6907335)). Qed.
Lemma lem6907337 : term377.
Proof. exact (EQ_MP (@lem6907336) (@lem0)). Qed.
Lemma lem6907338 : term381.
Proof. exact (@lem6907327 (@lem6907337)). Qed.
Lemma lem6907340 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907341 : term377 = term378.
Proof. exact (@lem6907340 (NUMERAL 0) term108). Qed.
Lemma lem6907342 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907343 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907344 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907343 h1) (fun h1 : term378 = True => @lem6907342)). Qed.
Lemma lem6907345 : term378 = True.
Proof. exact (EQ_MP (@lem6907344) (@lem6907342)). Qed.
Lemma lem6907346 : term377 = True.
Proof. exact (TRANS (@lem6907341) (@lem6907345)). Qed.
Lemma lem6907347 : True = term377.
Proof. exact (SYM (@lem6907346)). Qed.
Lemma lem6907348 : term377.
Proof. exact (EQ_MP (@lem6907347) (@lem0)). Qed.
Lemma lem6907349 : term382.
Proof. exact (@lem6907338 (@lem6907348)). Qed.
Lemma lem6907351 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907352 : term353 = term354.
Proof. exact (@lem6907351 term108 term108). Qed.
Lemma lem6907353 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907354 : term356 = term108.
Proof. exact (EQ_MP (@lem6907353) (@lem940073)). Qed.
Lemma lem6907355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907356 : term354 = term107.
Proof. exact (MK_COMB (@lem6907355) (@lem6907354)). Qed.
Lemma lem6907357 : term353 = term107.
Proof. exact (TRANS (@lem6907352) (@lem6907356)). Qed.
Lemma lem6907359 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907360 : term348 = term359.
Proof. exact (@lem6907359 term108 term108). Qed.
Lemma lem6907361 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907362 : term356 = term108.
Proof. exact (EQ_MP (@lem6907361) (@lem940073)). Qed.
Lemma lem6907363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907364 : term354 = term107.
Proof. exact (MK_COMB (@lem6907363) (@lem6907362)). Qed.
Lemma lem6907365 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907366 : term359 = term340.
Proof. exact (MK_COMB (@lem6907365) (@lem6907364)). Qed.
Lemma lem6907367 : term348 = term340.
Proof. exact (TRANS (@lem6907360) (@lem6907366)). Qed.
Lemma lem6907368 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907369 : term383 = term370.
Proof. exact (MK_COMB (@lem6907368) (@lem6907367)). Qed.
Lemma lem6907370 : term384 = term372.
Proof. exact (MK_COMB (@lem6907369) (@lem6907357)). Qed.
Lemma lem6907372 (m : nat) : (term385 m) = term375.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6907373 : term372 = term375.
Proof. exact (@lem6907372 term108). Qed.
Lemma lem6907374 : term384 = term375.
Proof. exact (TRANS (@lem6907370) (@lem6907373)). Qed.
Lemma lem6907375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907376 : term386 = term387.
Proof. exact (MK_COMB (@lem6907375) (@lem6907374)). Qed.
Lemma lem6907377 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907378 : term388 = term389.
Proof. exact (MK_COMB (@lem6907376) (@lem6907377)). Qed.
Lemma lem6907380 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907381 : term389 = term375.
Proof. exact (@lem6907380 term108). Qed.
Lemma lem6907382 : term388 = term375.
Proof. exact (TRANS (@lem6907378) (@lem6907381)). Qed.
Lemma lem6907384 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907385 : term353 = term354.
Proof. exact (@lem6907384 term108 term108). Qed.
Lemma lem6907386 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907387 : term356 = term108.
Proof. exact (EQ_MP (@lem6907386) (@lem940073)). Qed.
Lemma lem6907388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907389 : term354 = term107.
Proof. exact (MK_COMB (@lem6907388) (@lem6907387)). Qed.
Lemma lem6907390 : term353 = term107.
Proof. exact (TRANS (@lem6907385) (@lem6907389)). Qed.
Lemma lem6907391 : term387 = term387.
Proof. exact (eq_refl term387). Qed.
Lemma lem6907392 : term391 = term389.
Proof. exact (MK_COMB (@lem6907391) (@lem6907390)). Qed.
Lemma lem6907394 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907395 : term389 = term375.
Proof. exact (@lem6907394 term108). Qed.
Lemma lem6907396 : term391 = term375.
Proof. exact (TRANS (@lem6907392) (@lem6907395)). Qed.
Lemma lem6907397 : term375 = term391.
Proof. exact (SYM (@lem6907396)). Qed.
Lemma lem6907398 : term388 = term391.
Proof. exact (TRANS (@lem6907382) (@lem6907397)). Qed.
Lemma lem6907399 : term373 = term392.
Proof. exact (@lem6907349 (@lem6907398)). Qed.
Lemma lem6907400 : term372 = term392.
Proof. exact (TRANS (@lem6907315) (@lem6907399)). Qed.
Lemma lem6907402 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6907403 : term392 = term375.
Proof. exact (@lem6907402 term375). Qed.
Lemma lem6907404 : term372 = term375.
Proof. exact (TRANS (@lem6907400) (@lem6907403)). Qed.
Lemma lem6907405 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907406 : term393 = term387.
Proof. exact (MK_COMB (@lem6907405) (@lem6907404)). Qed.
Lemma lem6907407 (x : int) (y : int) (z : int) : (term129 x y z) = (term129 x y z).
Proof. exact (eq_refl (term129 x y z)). Qed.
Lemma lem6907408 (x : int) (y : int) (z : int) : (term421 x y z) = (term422 x y z).
Proof. exact (MK_COMB (@lem6907406) (@lem6907407 x y z)). Qed.
Lemma lem6907409 (x : int) (y : int) (z : int) : (term420 x y z) = (term422 x y z).
Proof. exact (TRANS (@lem6907306 x y z) (@lem6907408 x y z)). Qed.
Lemma lem6907410 (x : int) (y : int) (z : int) : (term422 x y z) = term375.
Proof. exact (@lem1982719 (term129 x y z)). Qed.
Lemma lem6907411 (x : int) (y : int) (z : int) : (term420 x y z) = term375.
Proof. exact (TRANS (@lem6907409 x y z) (@lem6907410 x y z)). Qed.
Lemma lem6907412 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907413 (x : int) (y : int) (z : int) : (term423 x y z) = term396.
Proof. exact (MK_COMB (@lem6907412) (@lem6907411 x y z)). Qed.
Lemma lem6907414 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem6907415 (x : int) (y : int) (z : int) : (term418 x y z) = term397.
Proof. exact (MK_COMB (@lem6907413 x y z) (@lem6907414)). Qed.
Lemma lem6907416 (x : int) (y : int) (z : int) : (term417 x y z) = term397.
Proof. exact (TRANS (@lem6907305 x y z) (@lem6907415 x y z)). Qed.
Lemma lem6907417 : term397 = term340.
Proof. exact (@lem1982721 term340). Qed.
Lemma lem6907418 (x : int) (y : int) (z : int) : (term417 x y z) = term340.
Proof. exact (TRANS (@lem6907416 x y z) (@lem6907417)). Qed.
Lemma lem6907419 (x : int) (y : int) (z : int) : (term412 x y z) = term340.
Proof. exact (TRANS (@lem6907304 x y z) (@lem6907418 x y z)). Qed.
Lemma lem6907420 (x : int) (y : int) (z : int) : (term411 x y z) = term340.
Proof. exact (TRANS (@lem6907259 x y z) (@lem6907419 x y z)). Qed.
Lemma lem6907421 (x : int) (y : int) (z : int) : (term410 x y z) = term340.
Proof. exact (TRANS (@lem6907258 x y z) (@lem6907420 x y z)). Qed.
Lemma lem6907422 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6907423 (x : int) (y : int) (z : int) : (term424 x y z) = term399.
Proof. exact (MK_COMB (@lem6907422) (@lem6907421 x y z)). Qed.
Lemma lem6907424 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem6907425 (x : int) (y : int) (z : int) : (term407 x y z) = term400.
Proof. exact (MK_COMB (@lem6907423 x y z) (@lem6907424)). Qed.
Lemma lem6907426 (x : int) (y : int) (z : int) : (term140 x y z) = term400.
Proof. exact (TRANS (@lem6907219 x y z) (@lem6907425 x y z)). Qed.
Lemma lem6907427 (x : int) (y : int) : (term248 x y) = term401.
Proof. exact (fun_ext (fun z : int => @lem6907426 x y z)). Qed.
Lemma lem6907428 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907429 (x : int) (y : int) : (term259 x y) = term402.
Proof. exact (MK_COMB (@lem6907428) (@lem6907427 x y)). Qed.
Lemma lem6907430 (x : int) : (term270 x) = term403.
Proof. exact (fun_ext (fun y : int => @lem6907429 x y)). Qed.
Lemma lem6907431 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907432 (x : int) : (term281 x) = term404.
Proof. exact (MK_COMB (@lem6907431) (@lem6907430 x)). Qed.
Lemma lem6907433 : term292 = term425.
Proof. exact (fun_ext (fun x : int => @lem6907432 x)). Qed.
Lemma lem6907434 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907435 : term303 = term426.
Proof. exact (MK_COMB (@lem6907434) (@lem6907433)). Qed.
Lemma lem6907436 (x : int) (y : int) (z : int) : (term153 x y z) = (term427 x y z).
Proof. exact (@lem1988287 (term129 x y z) (term150 x y z)). Qed.
Lemma lem6907437 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907454 (x : int) (y : int) (z : int) : (term139 x y z) = (term129 x y z).
Proof. exact (@lem1982745 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem6907455 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907456 (x : int) (y : int) (z : int) : (term149 x y z) = (term131 x y z).
Proof. exact (MK_COMB (@lem6907455) (@lem6907454 x y z)). Qed.
Lemma lem6907459 (x : int) (y : int) (z : int) : (term150 x y z) = (term132 x y z).
Proof. exact (MK_COMB (@lem6907456 x y z) (@lem6907437)). Qed.
Lemma lem6907474 (x : int) (y : int) (z : int) : (term409 x y z) = (term409 x y z).
Proof. exact (eq_refl (term409 x y z)). Qed.
Lemma lem6907475 (x : int) (y : int) (z : int) : (term428 x y z) = (term411 x y z).
Proof. exact (MK_COMB (@lem6907474 x y z) (@lem6907459 x y z)). Qed.
Lemma lem6907476 (x : int) (y : int) (z : int) : (term411 x y z) = (term412 x y z).
Proof. exact (@lem1982792 (term129 x y z) (term132 x y z)). Qed.
Lemma lem6907477 (x : int) (y : int) (z : int) : (term413 x y z) = (term414 x y z).
Proof. exact (@lem1982781 (term129 x y z) term340 term107). Qed.
Lemma lem6907479 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907480 : term107 = term342.
Proof. exact (@lem6907479 term108). Qed.
Lemma lem6907482 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907483 : term340 = term345.
Proof. exact (@lem6907482 term108). Qed.
Lemma lem6907484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907485 : term346 = term347.
Proof. exact (MK_COMB (@lem6907484) (@lem6907483)). Qed.
Lemma lem6907486 : term348 = term349.
Proof. exact (MK_COMB (@lem6907485) (@lem6907480)). Qed.
Lemma lem6907487 : term349 = term350.
Proof. exact (@lem1981613 term340 term107 term107 term107). Qed.
Lemma lem6907489 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907490 : term353 = term354.
Proof. exact (@lem6907489 term108 term108). Qed.
Lemma lem6907491 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907492 : term356 = term108.
Proof. exact (EQ_MP (@lem6907491) (@lem940073)). Qed.
Lemma lem6907493 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907494 : term354 = term107.
Proof. exact (MK_COMB (@lem6907493) (@lem6907492)). Qed.
Lemma lem6907495 : term353 = term107.
Proof. exact (TRANS (@lem6907490) (@lem6907494)). Qed.
Lemma lem6907497 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907498 : term348 = term359.
Proof. exact (@lem6907497 term108 term108). Qed.
Lemma lem6907499 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907500 : term356 = term108.
Proof. exact (EQ_MP (@lem6907499) (@lem940073)). Qed.
Lemma lem6907501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907502 : term354 = term107.
Proof. exact (MK_COMB (@lem6907501) (@lem6907500)). Qed.
Lemma lem6907503 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907504 : term359 = term340.
Proof. exact (MK_COMB (@lem6907503) (@lem6907502)). Qed.
Lemma lem6907505 : term348 = term340.
Proof. exact (TRANS (@lem6907498) (@lem6907504)). Qed.
Lemma lem6907506 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6907507 : term360 = term361.
Proof. exact (MK_COMB (@lem6907506) (@lem6907505)). Qed.
Lemma lem6907508 : term350 = term345.
Proof. exact (MK_COMB (@lem6907507) (@lem6907495)). Qed.
Lemma lem6907509 : term349 = term345.
Proof. exact (TRANS (@lem6907487) (@lem6907508)). Qed.
Lemma lem6907510 : term348 = term345.
Proof. exact (TRANS (@lem6907486) (@lem6907509)). Qed.
Lemma lem6907512 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6907513 : term345 = term340.
Proof. exact (@lem6907512 term340). Qed.
Lemma lem6907514 : term348 = term340.
Proof. exact (TRANS (@lem6907510) (@lem6907513)). Qed.
Lemma lem6907517 (x : int) (y : int) (z : int) : (term415 x y z) = (term415 x y z).
Proof. exact (eq_refl (term415 x y z)). Qed.
Lemma lem6907518 (x : int) (y : int) (z : int) : (term414 x y z) = (term416 x y z).
Proof. exact (MK_COMB (@lem6907517 x y z) (@lem6907514)). Qed.
Lemma lem6907519 (x : int) (y : int) (z : int) : (term413 x y z) = (term416 x y z).
Proof. exact (TRANS (@lem6907477 x y z) (@lem6907518 x y z)). Qed.
Lemma lem6907520 (x : int) (y : int) (z : int) : (term131 x y z) = (term131 x y z).
Proof. exact (eq_refl (term131 x y z)). Qed.
Lemma lem6907521 (x : int) (y : int) (z : int) : (term412 x y z) = (term417 x y z).
Proof. exact (MK_COMB (@lem6907520 x y z) (@lem6907519 x y z)). Qed.
Lemma lem6907522 (x : int) (y : int) (z : int) : (term417 x y z) = (term418 x y z).
Proof. exact (@lem1982763 (term129 x y z) (term419 x y z) term340). Qed.
Lemma lem6907523 (x : int) (y : int) (z : int) : (term420 x y z) = (term421 x y z).
Proof. exact (@lem1982715 term340 (term129 x y z)). Qed.
Lemma lem6907525 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907526 : term107 = term342.
Proof. exact (@lem6907525 term108). Qed.
Lemma lem6907528 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907529 : term340 = term345.
Proof. exact (@lem6907528 term108). Qed.
Lemma lem6907530 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907531 : term370 = term371.
Proof. exact (MK_COMB (@lem6907530) (@lem6907529)). Qed.
Lemma lem6907532 : term372 = term373.
Proof. exact (MK_COMB (@lem6907531) (@lem6907526)). Qed.
Lemma lem6907533 : term374.
Proof. exact (@lem1981473 term340 term107 term107 term107 term375 term107). Qed.
Lemma lem6907535 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907536 : term377 = term378.
Proof. exact (@lem6907535 (NUMERAL 0) term108). Qed.
Lemma lem6907537 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907538 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907539 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907538 h1) (fun h1 : term378 = True => @lem6907537)). Qed.
Lemma lem6907540 : term378 = True.
Proof. exact (EQ_MP (@lem6907539) (@lem6907537)). Qed.
Lemma lem6907541 : term377 = True.
Proof. exact (TRANS (@lem6907536) (@lem6907540)). Qed.
Lemma lem6907542 : True = term377.
Proof. exact (SYM (@lem6907541)). Qed.
Lemma lem6907543 : term377.
Proof. exact (EQ_MP (@lem6907542) (@lem0)). Qed.
Lemma lem6907544 : term380.
Proof. exact (@lem6907533 (@lem6907543)). Qed.
Lemma lem6907546 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907547 : term377 = term378.
Proof. exact (@lem6907546 (NUMERAL 0) term108). Qed.
Lemma lem6907548 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907549 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907550 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907549 h1) (fun h1 : term378 = True => @lem6907548)). Qed.
Lemma lem6907551 : term378 = True.
Proof. exact (EQ_MP (@lem6907550) (@lem6907548)). Qed.
Lemma lem6907552 : term377 = True.
Proof. exact (TRANS (@lem6907547) (@lem6907551)). Qed.
Lemma lem6907553 : True = term377.
Proof. exact (SYM (@lem6907552)). Qed.
Lemma lem6907554 : term377.
Proof. exact (EQ_MP (@lem6907553) (@lem0)). Qed.
Lemma lem6907555 : term381.
Proof. exact (@lem6907544 (@lem6907554)). Qed.
Lemma lem6907557 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907558 : term377 = term378.
Proof. exact (@lem6907557 (NUMERAL 0) term108). Qed.
Lemma lem6907559 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907560 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907561 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907560 h1) (fun h1 : term378 = True => @lem6907559)). Qed.
Lemma lem6907562 : term378 = True.
Proof. exact (EQ_MP (@lem6907561) (@lem6907559)). Qed.
Lemma lem6907563 : term377 = True.
Proof. exact (TRANS (@lem6907558) (@lem6907562)). Qed.
Lemma lem6907564 : True = term377.
Proof. exact (SYM (@lem6907563)). Qed.
Lemma lem6907565 : term377.
Proof. exact (EQ_MP (@lem6907564) (@lem0)). Qed.
Lemma lem6907566 : term382.
Proof. exact (@lem6907555 (@lem6907565)). Qed.
Lemma lem6907568 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907569 : term353 = term354.
Proof. exact (@lem6907568 term108 term108). Qed.
Lemma lem6907570 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907571 : term356 = term108.
Proof. exact (EQ_MP (@lem6907570) (@lem940073)). Qed.
Lemma lem6907572 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907573 : term354 = term107.
Proof. exact (MK_COMB (@lem6907572) (@lem6907571)). Qed.
Lemma lem6907574 : term353 = term107.
Proof. exact (TRANS (@lem6907569) (@lem6907573)). Qed.
Lemma lem6907576 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907577 : term348 = term359.
Proof. exact (@lem6907576 term108 term108). Qed.
Lemma lem6907578 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907579 : term356 = term108.
Proof. exact (EQ_MP (@lem6907578) (@lem940073)). Qed.
Lemma lem6907580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907581 : term354 = term107.
Proof. exact (MK_COMB (@lem6907580) (@lem6907579)). Qed.
Lemma lem6907582 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907583 : term359 = term340.
Proof. exact (MK_COMB (@lem6907582) (@lem6907581)). Qed.
Lemma lem6907584 : term348 = term340.
Proof. exact (TRANS (@lem6907577) (@lem6907583)). Qed.
Lemma lem6907585 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907586 : term383 = term370.
Proof. exact (MK_COMB (@lem6907585) (@lem6907584)). Qed.
Lemma lem6907587 : term384 = term372.
Proof. exact (MK_COMB (@lem6907586) (@lem6907574)). Qed.
Lemma lem6907589 (m : nat) : (term385 m) = term375.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6907590 : term372 = term375.
Proof. exact (@lem6907589 term108). Qed.
Lemma lem6907591 : term384 = term375.
Proof. exact (TRANS (@lem6907587) (@lem6907590)). Qed.
Lemma lem6907592 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907593 : term386 = term387.
Proof. exact (MK_COMB (@lem6907592) (@lem6907591)). Qed.
Lemma lem6907594 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907595 : term388 = term389.
Proof. exact (MK_COMB (@lem6907593) (@lem6907594)). Qed.
Lemma lem6907597 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907598 : term389 = term375.
Proof. exact (@lem6907597 term108). Qed.
Lemma lem6907599 : term388 = term375.
Proof. exact (TRANS (@lem6907595) (@lem6907598)). Qed.
Lemma lem6907601 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907602 : term353 = term354.
Proof. exact (@lem6907601 term108 term108). Qed.
Lemma lem6907603 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907604 : term356 = term108.
Proof. exact (EQ_MP (@lem6907603) (@lem940073)). Qed.
Lemma lem6907605 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907606 : term354 = term107.
Proof. exact (MK_COMB (@lem6907605) (@lem6907604)). Qed.
Lemma lem6907607 : term353 = term107.
Proof. exact (TRANS (@lem6907602) (@lem6907606)). Qed.
Lemma lem6907608 : term387 = term387.
Proof. exact (eq_refl term387). Qed.
Lemma lem6907609 : term391 = term389.
Proof. exact (MK_COMB (@lem6907608) (@lem6907607)). Qed.
Lemma lem6907611 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907612 : term389 = term375.
Proof. exact (@lem6907611 term108). Qed.
Lemma lem6907613 : term391 = term375.
Proof. exact (TRANS (@lem6907609) (@lem6907612)). Qed.
Lemma lem6907614 : term375 = term391.
Proof. exact (SYM (@lem6907613)). Qed.
Lemma lem6907615 : term388 = term391.
Proof. exact (TRANS (@lem6907599) (@lem6907614)). Qed.
Lemma lem6907616 : term373 = term392.
Proof. exact (@lem6907566 (@lem6907615)). Qed.
Lemma lem6907617 : term372 = term392.
Proof. exact (TRANS (@lem6907532) (@lem6907616)). Qed.
Lemma lem6907619 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6907620 : term392 = term375.
Proof. exact (@lem6907619 term375). Qed.
Lemma lem6907621 : term372 = term375.
Proof. exact (TRANS (@lem6907617) (@lem6907620)). Qed.
Lemma lem6907622 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907623 : term393 = term387.
Proof. exact (MK_COMB (@lem6907622) (@lem6907621)). Qed.
Lemma lem6907624 (x : int) (y : int) (z : int) : (term129 x y z) = (term129 x y z).
Proof. exact (eq_refl (term129 x y z)). Qed.
Lemma lem6907625 (x : int) (y : int) (z : int) : (term421 x y z) = (term422 x y z).
Proof. exact (MK_COMB (@lem6907623) (@lem6907624 x y z)). Qed.
Lemma lem6907626 (x : int) (y : int) (z : int) : (term420 x y z) = (term422 x y z).
Proof. exact (TRANS (@lem6907523 x y z) (@lem6907625 x y z)). Qed.
Lemma lem6907627 (x : int) (y : int) (z : int) : (term422 x y z) = term375.
Proof. exact (@lem1982719 (term129 x y z)). Qed.
Lemma lem6907628 (x : int) (y : int) (z : int) : (term420 x y z) = term375.
Proof. exact (TRANS (@lem6907626 x y z) (@lem6907627 x y z)). Qed.
Lemma lem6907629 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907630 (x : int) (y : int) (z : int) : (term423 x y z) = term396.
Proof. exact (MK_COMB (@lem6907629) (@lem6907628 x y z)). Qed.
Lemma lem6907631 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem6907632 (x : int) (y : int) (z : int) : (term418 x y z) = term397.
Proof. exact (MK_COMB (@lem6907630 x y z) (@lem6907631)). Qed.
Lemma lem6907633 (x : int) (y : int) (z : int) : (term417 x y z) = term397.
Proof. exact (TRANS (@lem6907522 x y z) (@lem6907632 x y z)). Qed.
Lemma lem6907634 : term397 = term340.
Proof. exact (@lem1982721 term340). Qed.
Lemma lem6907635 (x : int) (y : int) (z : int) : (term417 x y z) = term340.
Proof. exact (TRANS (@lem6907633 x y z) (@lem6907634)). Qed.
Lemma lem6907636 (x : int) (y : int) (z : int) : (term412 x y z) = term340.
Proof. exact (TRANS (@lem6907521 x y z) (@lem6907635 x y z)). Qed.
Lemma lem6907637 (x : int) (y : int) (z : int) : (term411 x y z) = term340.
Proof. exact (TRANS (@lem6907476 x y z) (@lem6907636 x y z)). Qed.
Lemma lem6907638 (x : int) (y : int) (z : int) : (term428 x y z) = term340.
Proof. exact (TRANS (@lem6907475 x y z) (@lem6907637 x y z)). Qed.
Lemma lem6907639 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6907640 (x : int) (y : int) (z : int) : (term429 x y z) = term399.
Proof. exact (MK_COMB (@lem6907639) (@lem6907638 x y z)). Qed.
Lemma lem6907641 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem6907642 (x : int) (y : int) (z : int) : (term427 x y z) = term400.
Proof. exact (MK_COMB (@lem6907640 x y z) (@lem6907641)). Qed.
Lemma lem6907643 (x : int) (y : int) (z : int) : (term153 x y z) = term400.
Proof. exact (TRANS (@lem6907436 x y z) (@lem6907642 x y z)). Qed.
Lemma lem6907644 (x : int) (y : int) : (term249 x y) = term401.
Proof. exact (fun_ext (fun z : int => @lem6907643 x y z)). Qed.
Lemma lem6907645 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907646 (x : int) (y : int) : (term264 x y) = term402.
Proof. exact (MK_COMB (@lem6907645) (@lem6907644 x y)). Qed.
Lemma lem6907647 (x : int) : (term271 x) = term403.
Proof. exact (fun_ext (fun y : int => @lem6907646 x y)). Qed.
Lemma lem6907648 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907649 (x : int) : (term286 x) = term404.
Proof. exact (MK_COMB (@lem6907648) (@lem6907647 x)). Qed.
Lemma lem6907650 : term293 = term425.
Proof. exact (fun_ext (fun x : int => @lem6907649 x)). Qed.
Lemma lem6907651 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907652 : term308 = term426.
Proof. exact (MK_COMB (@lem6907651) (@lem6907650)). Qed.
Lemma lem6907653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6907654 : term305 = term430.
Proof. exact (MK_COMB (@lem6907653) (@lem6907435)). Qed.
Lemma lem6907655 : term309 = term431.
Proof. exact (MK_COMB (@lem6907654) (@lem6907652)). Qed.
Lemma lem6907656 (x : int) : (term177 x) = (term432 x).
Proof. exact (@lem1988287 (real_of_int x) (term174 x)). Qed.
Lemma lem6907657 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907664 (x : int) : (term171 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem6907665 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907666 (x : int) : (term173 x) = (term185 x).
Proof. exact (MK_COMB (@lem6907665) (@lem6907664 x)). Qed.
Lemma lem6907669 (x : int) : (term174 x) = (term186 x).
Proof. exact (MK_COMB (@lem6907666 x) (@lem6907657)). Qed.
Lemma lem6907672 (x : int) : (term433 x) = (term433 x).
Proof. exact (eq_refl (term433 x)). Qed.
Lemma lem6907673 (x : int) : (term434 x) = (term435 x).
Proof. exact (MK_COMB (@lem6907672 x) (@lem6907669 x)). Qed.
Lemma lem6907674 (x : int) : (term435 x) = (term436 x).
Proof. exact (@lem1982792 (real_of_int x) (term186 x)). Qed.
Lemma lem6907675 (x : int) : (term437 x) = (term438 x).
Proof. exact (@lem1982781 (real_of_int x) term340 term107). Qed.
Lemma lem6907677 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907678 : term107 = term342.
Proof. exact (@lem6907677 term108). Qed.
Lemma lem6907680 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907681 : term340 = term345.
Proof. exact (@lem6907680 term108). Qed.
Lemma lem6907682 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907683 : term346 = term347.
Proof. exact (MK_COMB (@lem6907682) (@lem6907681)). Qed.
Lemma lem6907684 : term348 = term349.
Proof. exact (MK_COMB (@lem6907683) (@lem6907678)). Qed.
Lemma lem6907685 : term349 = term350.
Proof. exact (@lem1981613 term340 term107 term107 term107). Qed.
Lemma lem6907687 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907688 : term353 = term354.
Proof. exact (@lem6907687 term108 term108). Qed.
Lemma lem6907689 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907690 : term356 = term108.
Proof. exact (EQ_MP (@lem6907689) (@lem940073)). Qed.
Lemma lem6907691 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907692 : term354 = term107.
Proof. exact (MK_COMB (@lem6907691) (@lem6907690)). Qed.
Lemma lem6907693 : term353 = term107.
Proof. exact (TRANS (@lem6907688) (@lem6907692)). Qed.
Lemma lem6907695 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907696 : term348 = term359.
Proof. exact (@lem6907695 term108 term108). Qed.
Lemma lem6907697 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907698 : term356 = term108.
Proof. exact (EQ_MP (@lem6907697) (@lem940073)). Qed.
Lemma lem6907699 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907700 : term354 = term107.
Proof. exact (MK_COMB (@lem6907699) (@lem6907698)). Qed.
Lemma lem6907701 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907702 : term359 = term340.
Proof. exact (MK_COMB (@lem6907701) (@lem6907700)). Qed.
Lemma lem6907703 : term348 = term340.
Proof. exact (TRANS (@lem6907696) (@lem6907702)). Qed.
Lemma lem6907704 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6907705 : term360 = term361.
Proof. exact (MK_COMB (@lem6907704) (@lem6907703)). Qed.
Lemma lem6907706 : term350 = term345.
Proof. exact (MK_COMB (@lem6907705) (@lem6907693)). Qed.
Lemma lem6907707 : term349 = term345.
Proof. exact (TRANS (@lem6907685) (@lem6907706)). Qed.
Lemma lem6907708 : term348 = term345.
Proof. exact (TRANS (@lem6907684) (@lem6907707)). Qed.
Lemma lem6907710 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6907711 : term345 = term340.
Proof. exact (@lem6907710 term340). Qed.
Lemma lem6907712 : term348 = term340.
Proof. exact (TRANS (@lem6907708) (@lem6907711)). Qed.
Lemma lem6907715 (x : int) : (term439 x) = (term439 x).
Proof. exact (eq_refl (term439 x)). Qed.
Lemma lem6907716 (x : int) : (term438 x) = (term440 x).
Proof. exact (MK_COMB (@lem6907715 x) (@lem6907712)). Qed.
Lemma lem6907717 (x : int) : (term437 x) = (term440 x).
Proof. exact (TRANS (@lem6907675 x) (@lem6907716 x)). Qed.
Lemma lem6907718 (x : int) : (term185 x) = (term185 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem6907719 (x : int) : (term436 x) = (term441 x).
Proof. exact (MK_COMB (@lem6907718 x) (@lem6907717 x)). Qed.
Lemma lem6907720 (x : int) : (term441 x) = (term442 x).
Proof. exact (@lem1982763 (real_of_int x) (term443 x) term340). Qed.
Lemma lem6907721 (x : int) : (term444 x) = (term445 x).
Proof. exact (@lem1982715 term340 (real_of_int x)). Qed.
Lemma lem6907723 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907724 : term107 = term342.
Proof. exact (@lem6907723 term108). Qed.
Lemma lem6907726 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907727 : term340 = term345.
Proof. exact (@lem6907726 term108). Qed.
Lemma lem6907728 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907729 : term370 = term371.
Proof. exact (MK_COMB (@lem6907728) (@lem6907727)). Qed.
Lemma lem6907730 : term372 = term373.
Proof. exact (MK_COMB (@lem6907729) (@lem6907724)). Qed.
Lemma lem6907731 : term374.
Proof. exact (@lem1981473 term340 term107 term107 term107 term375 term107). Qed.
Lemma lem6907733 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907734 : term377 = term378.
Proof. exact (@lem6907733 (NUMERAL 0) term108). Qed.
Lemma lem6907735 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907736 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907737 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907736 h1) (fun h1 : term378 = True => @lem6907735)). Qed.
Lemma lem6907738 : term378 = True.
Proof. exact (EQ_MP (@lem6907737) (@lem6907735)). Qed.
Lemma lem6907739 : term377 = True.
Proof. exact (TRANS (@lem6907734) (@lem6907738)). Qed.
Lemma lem6907740 : True = term377.
Proof. exact (SYM (@lem6907739)). Qed.
Lemma lem6907741 : term377.
Proof. exact (EQ_MP (@lem6907740) (@lem0)). Qed.
Lemma lem6907742 : term380.
Proof. exact (@lem6907731 (@lem6907741)). Qed.
Lemma lem6907744 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907745 : term377 = term378.
Proof. exact (@lem6907744 (NUMERAL 0) term108). Qed.
Lemma lem6907746 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907747 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907748 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907747 h1) (fun h1 : term378 = True => @lem6907746)). Qed.
Lemma lem6907749 : term378 = True.
Proof. exact (EQ_MP (@lem6907748) (@lem6907746)). Qed.
Lemma lem6907750 : term377 = True.
Proof. exact (TRANS (@lem6907745) (@lem6907749)). Qed.
Lemma lem6907751 : True = term377.
Proof. exact (SYM (@lem6907750)). Qed.
Lemma lem6907752 : term377.
Proof. exact (EQ_MP (@lem6907751) (@lem0)). Qed.
Lemma lem6907753 : term381.
Proof. exact (@lem6907742 (@lem6907752)). Qed.
Lemma lem6907755 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907756 : term377 = term378.
Proof. exact (@lem6907755 (NUMERAL 0) term108). Qed.
Lemma lem6907757 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907758 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907759 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907758 h1) (fun h1 : term378 = True => @lem6907757)). Qed.
Lemma lem6907760 : term378 = True.
Proof. exact (EQ_MP (@lem6907759) (@lem6907757)). Qed.
Lemma lem6907761 : term377 = True.
Proof. exact (TRANS (@lem6907756) (@lem6907760)). Qed.
Lemma lem6907762 : True = term377.
Proof. exact (SYM (@lem6907761)). Qed.
Lemma lem6907763 : term377.
Proof. exact (EQ_MP (@lem6907762) (@lem0)). Qed.
Lemma lem6907764 : term382.
Proof. exact (@lem6907753 (@lem6907763)). Qed.
Lemma lem6907766 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907767 : term353 = term354.
Proof. exact (@lem6907766 term108 term108). Qed.
Lemma lem6907768 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907769 : term356 = term108.
Proof. exact (EQ_MP (@lem6907768) (@lem940073)). Qed.
Lemma lem6907770 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907771 : term354 = term107.
Proof. exact (MK_COMB (@lem6907770) (@lem6907769)). Qed.
Lemma lem6907772 : term353 = term107.
Proof. exact (TRANS (@lem6907767) (@lem6907771)). Qed.
Lemma lem6907774 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907775 : term348 = term359.
Proof. exact (@lem6907774 term108 term108). Qed.
Lemma lem6907776 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907777 : term356 = term108.
Proof. exact (EQ_MP (@lem6907776) (@lem940073)). Qed.
Lemma lem6907778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907779 : term354 = term107.
Proof. exact (MK_COMB (@lem6907778) (@lem6907777)). Qed.
Lemma lem6907780 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907781 : term359 = term340.
Proof. exact (MK_COMB (@lem6907780) (@lem6907779)). Qed.
Lemma lem6907782 : term348 = term340.
Proof. exact (TRANS (@lem6907775) (@lem6907781)). Qed.
Lemma lem6907783 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907784 : term383 = term370.
Proof. exact (MK_COMB (@lem6907783) (@lem6907782)). Qed.
Lemma lem6907785 : term384 = term372.
Proof. exact (MK_COMB (@lem6907784) (@lem6907772)). Qed.
Lemma lem6907787 (m : nat) : (term385 m) = term375.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6907788 : term372 = term375.
Proof. exact (@lem6907787 term108). Qed.
Lemma lem6907789 : term384 = term375.
Proof. exact (TRANS (@lem6907785) (@lem6907788)). Qed.
Lemma lem6907790 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907791 : term386 = term387.
Proof. exact (MK_COMB (@lem6907790) (@lem6907789)). Qed.
Lemma lem6907792 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907793 : term388 = term389.
Proof. exact (MK_COMB (@lem6907791) (@lem6907792)). Qed.
Lemma lem6907795 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907796 : term389 = term375.
Proof. exact (@lem6907795 term108). Qed.
Lemma lem6907797 : term388 = term375.
Proof. exact (TRANS (@lem6907793) (@lem6907796)). Qed.
Lemma lem6907799 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907800 : term353 = term354.
Proof. exact (@lem6907799 term108 term108). Qed.
Lemma lem6907801 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907802 : term356 = term108.
Proof. exact (EQ_MP (@lem6907801) (@lem940073)). Qed.
Lemma lem6907803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907804 : term354 = term107.
Proof. exact (MK_COMB (@lem6907803) (@lem6907802)). Qed.
Lemma lem6907805 : term353 = term107.
Proof. exact (TRANS (@lem6907800) (@lem6907804)). Qed.
Lemma lem6907806 : term387 = term387.
Proof. exact (eq_refl term387). Qed.
Lemma lem6907807 : term391 = term389.
Proof. exact (MK_COMB (@lem6907806) (@lem6907805)). Qed.
Lemma lem6907809 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907810 : term389 = term375.
Proof. exact (@lem6907809 term108). Qed.
Lemma lem6907811 : term391 = term375.
Proof. exact (TRANS (@lem6907807) (@lem6907810)). Qed.
Lemma lem6907812 : term375 = term391.
Proof. exact (SYM (@lem6907811)). Qed.
Lemma lem6907813 : term388 = term391.
Proof. exact (TRANS (@lem6907797) (@lem6907812)). Qed.
Lemma lem6907814 : term373 = term392.
Proof. exact (@lem6907764 (@lem6907813)). Qed.
Lemma lem6907815 : term372 = term392.
Proof. exact (TRANS (@lem6907730) (@lem6907814)). Qed.
Lemma lem6907817 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6907818 : term392 = term375.
Proof. exact (@lem6907817 term375). Qed.
Lemma lem6907819 : term372 = term375.
Proof. exact (TRANS (@lem6907815) (@lem6907818)). Qed.
Lemma lem6907820 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907821 : term393 = term387.
Proof. exact (MK_COMB (@lem6907820) (@lem6907819)). Qed.
Lemma lem6907822 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6907823 (x : int) : (term445 x) = (term446 x).
Proof. exact (MK_COMB (@lem6907821) (@lem6907822 x)). Qed.
Lemma lem6907824 (x : int) : (term444 x) = (term446 x).
Proof. exact (TRANS (@lem6907721 x) (@lem6907823 x)). Qed.
Lemma lem6907825 (x : int) : (term446 x) = term375.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6907826 (x : int) : (term444 x) = term375.
Proof. exact (TRANS (@lem6907824 x) (@lem6907825 x)). Qed.
Lemma lem6907827 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907828 (x : int) : (term447 x) = term396.
Proof. exact (MK_COMB (@lem6907827) (@lem6907826 x)). Qed.
Lemma lem6907829 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem6907830 (x : int) : (term442 x) = term397.
Proof. exact (MK_COMB (@lem6907828 x) (@lem6907829)). Qed.
Lemma lem6907831 (x : int) : (term441 x) = term397.
Proof. exact (TRANS (@lem6907720 x) (@lem6907830 x)). Qed.
Lemma lem6907832 : term397 = term340.
Proof. exact (@lem1982721 term340). Qed.
Lemma lem6907833 (x : int) : (term441 x) = term340.
Proof. exact (TRANS (@lem6907831 x) (@lem6907832)). Qed.
Lemma lem6907834 (x : int) : (term436 x) = term340.
Proof. exact (TRANS (@lem6907719 x) (@lem6907833 x)). Qed.
Lemma lem6907835 (x : int) : (term435 x) = term340.
Proof. exact (TRANS (@lem6907674 x) (@lem6907834 x)). Qed.
Lemma lem6907836 (x : int) : (term434 x) = term340.
Proof. exact (TRANS (@lem6907673 x) (@lem6907835 x)). Qed.
Lemma lem6907837 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6907838 (x : int) : (term448 x) = term399.
Proof. exact (MK_COMB (@lem6907837) (@lem6907836 x)). Qed.
Lemma lem6907839 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem6907840 (x : int) : (term432 x) = term400.
Proof. exact (MK_COMB (@lem6907838 x) (@lem6907839)). Qed.
Lemma lem6907841 (x : int) : (term177 x) = term400.
Proof. exact (TRANS (@lem6907656 x) (@lem6907840 x)). Qed.
Lemma lem6907842 : term313 = term401.
Proof. exact (fun_ext (fun x : int => @lem6907841 x)). Qed.
Lemma lem6907843 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6907844 : term324 = term402.
Proof. exact (MK_COMB (@lem6907843) (@lem6907842)). Qed.
Lemma lem6907845 (x : int) : (term189 x) = (term449 x).
Proof. exact (@lem1988287 (term171 x) (term186 x)). Qed.
Lemma lem6907852 (x : int) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem6907859 (x : int) : (term171 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem6907860 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6907861 (x : int) : (term450 x) = (term433 x).
Proof. exact (MK_COMB (@lem6907860) (@lem6907859 x)). Qed.
Lemma lem6907862 (x : int) : (term451 x) = (term435 x).
Proof. exact (MK_COMB (@lem6907861 x) (@lem6907852 x)). Qed.
Lemma lem6907863 (x : int) : (term435 x) = (term436 x).
Proof. exact (@lem1982792 (real_of_int x) (term186 x)). Qed.
Lemma lem6907864 (x : int) : (term437 x) = (term438 x).
Proof. exact (@lem1982781 (real_of_int x) term340 term107). Qed.
Lemma lem6907866 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907867 : term107 = term342.
Proof. exact (@lem6907866 term108). Qed.
Lemma lem6907869 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907870 : term340 = term345.
Proof. exact (@lem6907869 term108). Qed.
Lemma lem6907871 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907872 : term346 = term347.
Proof. exact (MK_COMB (@lem6907871) (@lem6907870)). Qed.
Lemma lem6907873 : term348 = term349.
Proof. exact (MK_COMB (@lem6907872) (@lem6907867)). Qed.
Lemma lem6907874 : term349 = term350.
Proof. exact (@lem1981613 term340 term107 term107 term107). Qed.
Lemma lem6907876 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907877 : term353 = term354.
Proof. exact (@lem6907876 term108 term108). Qed.
Lemma lem6907878 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907879 : term356 = term108.
Proof. exact (EQ_MP (@lem6907878) (@lem940073)). Qed.
Lemma lem6907880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907881 : term354 = term107.
Proof. exact (MK_COMB (@lem6907880) (@lem6907879)). Qed.
Lemma lem6907882 : term353 = term107.
Proof. exact (TRANS (@lem6907877) (@lem6907881)). Qed.
Lemma lem6907884 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907885 : term348 = term359.
Proof. exact (@lem6907884 term108 term108). Qed.
Lemma lem6907886 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907887 : term356 = term108.
Proof. exact (EQ_MP (@lem6907886) (@lem940073)). Qed.
Lemma lem6907888 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907889 : term354 = term107.
Proof. exact (MK_COMB (@lem6907888) (@lem6907887)). Qed.
Lemma lem6907890 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907891 : term359 = term340.
Proof. exact (MK_COMB (@lem6907890) (@lem6907889)). Qed.
Lemma lem6907892 : term348 = term340.
Proof. exact (TRANS (@lem6907885) (@lem6907891)). Qed.
Lemma lem6907893 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6907894 : term360 = term361.
Proof. exact (MK_COMB (@lem6907893) (@lem6907892)). Qed.
Lemma lem6907895 : term350 = term345.
Proof. exact (MK_COMB (@lem6907894) (@lem6907882)). Qed.
Lemma lem6907896 : term349 = term345.
Proof. exact (TRANS (@lem6907874) (@lem6907895)). Qed.
Lemma lem6907897 : term348 = term345.
Proof. exact (TRANS (@lem6907873) (@lem6907896)). Qed.
Lemma lem6907899 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6907900 : term345 = term340.
Proof. exact (@lem6907899 term340). Qed.
Lemma lem6907901 : term348 = term340.
Proof. exact (TRANS (@lem6907897) (@lem6907900)). Qed.
Lemma lem6907904 (x : int) : (term439 x) = (term439 x).
Proof. exact (eq_refl (term439 x)). Qed.
Lemma lem6907905 (x : int) : (term438 x) = (term440 x).
Proof. exact (MK_COMB (@lem6907904 x) (@lem6907901)). Qed.
Lemma lem6907906 (x : int) : (term437 x) = (term440 x).
Proof. exact (TRANS (@lem6907864 x) (@lem6907905 x)). Qed.
Lemma lem6907907 (x : int) : (term185 x) = (term185 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem6907908 (x : int) : (term436 x) = (term441 x).
Proof. exact (MK_COMB (@lem6907907 x) (@lem6907906 x)). Qed.
Lemma lem6907909 (x : int) : (term441 x) = (term442 x).
Proof. exact (@lem1982763 (real_of_int x) (term443 x) term340). Qed.
Lemma lem6907910 (x : int) : (term444 x) = (term445 x).
Proof. exact (@lem1982715 term340 (real_of_int x)). Qed.
Lemma lem6907912 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6907913 : term107 = term342.
Proof. exact (@lem6907912 term108). Qed.
Lemma lem6907915 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6907916 : term340 = term345.
Proof. exact (@lem6907915 term108). Qed.
Lemma lem6907917 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907918 : term370 = term371.
Proof. exact (MK_COMB (@lem6907917) (@lem6907916)). Qed.
Lemma lem6907919 : term372 = term373.
Proof. exact (MK_COMB (@lem6907918) (@lem6907913)). Qed.
Lemma lem6907920 : term374.
Proof. exact (@lem1981473 term340 term107 term107 term107 term375 term107). Qed.
Lemma lem6907922 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907923 : term377 = term378.
Proof. exact (@lem6907922 (NUMERAL 0) term108). Qed.
Lemma lem6907924 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907925 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907926 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907925 h1) (fun h1 : term378 = True => @lem6907924)). Qed.
Lemma lem6907927 : term378 = True.
Proof. exact (EQ_MP (@lem6907926) (@lem6907924)). Qed.
Lemma lem6907928 : term377 = True.
Proof. exact (TRANS (@lem6907923) (@lem6907927)). Qed.
Lemma lem6907929 : True = term377.
Proof. exact (SYM (@lem6907928)). Qed.
Lemma lem6907930 : term377.
Proof. exact (EQ_MP (@lem6907929) (@lem0)). Qed.
Lemma lem6907931 : term380.
Proof. exact (@lem6907920 (@lem6907930)). Qed.
Lemma lem6907933 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907934 : term377 = term378.
Proof. exact (@lem6907933 (NUMERAL 0) term108). Qed.
Lemma lem6907935 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907936 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907937 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907936 h1) (fun h1 : term378 = True => @lem6907935)). Qed.
Lemma lem6907938 : term378 = True.
Proof. exact (EQ_MP (@lem6907937) (@lem6907935)). Qed.
Lemma lem6907939 : term377 = True.
Proof. exact (TRANS (@lem6907934) (@lem6907938)). Qed.
Lemma lem6907940 : True = term377.
Proof. exact (SYM (@lem6907939)). Qed.
Lemma lem6907941 : term377.
Proof. exact (EQ_MP (@lem6907940) (@lem0)). Qed.
Lemma lem6907942 : term381.
Proof. exact (@lem6907931 (@lem6907941)). Qed.
Lemma lem6907944 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6907945 : term377 = term378.
Proof. exact (@lem6907944 (NUMERAL 0) term108). Qed.
Lemma lem6907946 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6907947 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6907948 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6907947 h1) (fun h1 : term378 = True => @lem6907946)). Qed.
Lemma lem6907949 : term378 = True.
Proof. exact (EQ_MP (@lem6907948) (@lem6907946)). Qed.
Lemma lem6907950 : term377 = True.
Proof. exact (TRANS (@lem6907945) (@lem6907949)). Qed.
Lemma lem6907951 : True = term377.
Proof. exact (SYM (@lem6907950)). Qed.
Lemma lem6907952 : term377.
Proof. exact (EQ_MP (@lem6907951) (@lem0)). Qed.
Lemma lem6907953 : term382.
Proof. exact (@lem6907942 (@lem6907952)). Qed.
Lemma lem6907955 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907956 : term353 = term354.
Proof. exact (@lem6907955 term108 term108). Qed.
Lemma lem6907957 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907958 : term356 = term108.
Proof. exact (EQ_MP (@lem6907957) (@lem940073)). Qed.
Lemma lem6907959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907960 : term354 = term107.
Proof. exact (MK_COMB (@lem6907959) (@lem6907958)). Qed.
Lemma lem6907961 : term353 = term107.
Proof. exact (TRANS (@lem6907956) (@lem6907960)). Qed.
Lemma lem6907963 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6907964 : term348 = term359.
Proof. exact (@lem6907963 term108 term108). Qed.
Lemma lem6907965 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907966 : term356 = term108.
Proof. exact (EQ_MP (@lem6907965) (@lem940073)). Qed.
Lemma lem6907967 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907968 : term354 = term107.
Proof. exact (MK_COMB (@lem6907967) (@lem6907966)). Qed.
Lemma lem6907969 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6907970 : term359 = term340.
Proof. exact (MK_COMB (@lem6907969) (@lem6907968)). Qed.
Lemma lem6907971 : term348 = term340.
Proof. exact (TRANS (@lem6907964) (@lem6907970)). Qed.
Lemma lem6907972 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6907973 : term383 = term370.
Proof. exact (MK_COMB (@lem6907972) (@lem6907971)). Qed.
Lemma lem6907974 : term384 = term372.
Proof. exact (MK_COMB (@lem6907973) (@lem6907961)). Qed.
Lemma lem6907976 (m : nat) : (term385 m) = term375.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6907977 : term372 = term375.
Proof. exact (@lem6907976 term108). Qed.
Lemma lem6907978 : term384 = term375.
Proof. exact (TRANS (@lem6907974) (@lem6907977)). Qed.
Lemma lem6907979 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6907980 : term386 = term387.
Proof. exact (MK_COMB (@lem6907979) (@lem6907978)). Qed.
Lemma lem6907981 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem6907982 : term388 = term389.
Proof. exact (MK_COMB (@lem6907980) (@lem6907981)). Qed.
Lemma lem6907984 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907985 : term389 = term375.
Proof. exact (@lem6907984 term108). Qed.
Lemma lem6907986 : term388 = term375.
Proof. exact (TRANS (@lem6907982) (@lem6907985)). Qed.
Lemma lem6907988 (m : nat) (n : nat) : (term351 m n) = (term352 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6907989 : term353 = term354.
Proof. exact (@lem6907988 term108 term108). Qed.
Lemma lem6907990 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6907991 : term356 = term108.
Proof. exact (EQ_MP (@lem6907990) (@lem940073)). Qed.
Lemma lem6907992 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6907993 : term354 = term107.
Proof. exact (MK_COMB (@lem6907992) (@lem6907991)). Qed.
Lemma lem6907994 : term353 = term107.
Proof. exact (TRANS (@lem6907989) (@lem6907993)). Qed.
Lemma lem6907995 : term387 = term387.
Proof. exact (eq_refl term387). Qed.
Lemma lem6907996 : term391 = term389.
Proof. exact (MK_COMB (@lem6907995) (@lem6907994)). Qed.
Lemma lem6907998 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6907999 : term389 = term375.
Proof. exact (@lem6907998 term108). Qed.
Lemma lem6908000 : term391 = term375.
Proof. exact (TRANS (@lem6907996) (@lem6907999)). Qed.
Lemma lem6908001 : term375 = term391.
Proof. exact (SYM (@lem6908000)). Qed.
Lemma lem6908002 : term388 = term391.
Proof. exact (TRANS (@lem6907986) (@lem6908001)). Qed.
Lemma lem6908003 : term373 = term392.
Proof. exact (@lem6907953 (@lem6908002)). Qed.
Lemma lem6908004 : term372 = term392.
Proof. exact (TRANS (@lem6907919) (@lem6908003)). Qed.
Lemma lem6908006 (x : real) : (term362 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6908007 : term392 = term375.
Proof. exact (@lem6908006 term375). Qed.
Lemma lem6908008 : term372 = term375.
Proof. exact (TRANS (@lem6908004) (@lem6908007)). Qed.
Lemma lem6908009 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6908010 : term393 = term387.
Proof. exact (MK_COMB (@lem6908009) (@lem6908008)). Qed.
Lemma lem6908011 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6908012 (x : int) : (term445 x) = (term446 x).
Proof. exact (MK_COMB (@lem6908010) (@lem6908011 x)). Qed.
Lemma lem6908013 (x : int) : (term444 x) = (term446 x).
Proof. exact (TRANS (@lem6907910 x) (@lem6908012 x)). Qed.
Lemma lem6908014 (x : int) : (term446 x) = term375.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6908015 (x : int) : (term444 x) = term375.
Proof. exact (TRANS (@lem6908013 x) (@lem6908014 x)). Qed.
Lemma lem6908016 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6908017 (x : int) : (term447 x) = term396.
Proof. exact (MK_COMB (@lem6908016) (@lem6908015 x)). Qed.
Lemma lem6908018 : term340 = term340.
Proof. exact (eq_refl term340). Qed.
Lemma lem6908019 (x : int) : (term442 x) = term397.
Proof. exact (MK_COMB (@lem6908017 x) (@lem6908018)). Qed.
Lemma lem6908020 (x : int) : (term441 x) = term397.
Proof. exact (TRANS (@lem6907909 x) (@lem6908019 x)). Qed.
Lemma lem6908021 : term397 = term340.
Proof. exact (@lem1982721 term340). Qed.
Lemma lem6908022 (x : int) : (term441 x) = term340.
Proof. exact (TRANS (@lem6908020 x) (@lem6908021)). Qed.
Lemma lem6908023 (x : int) : (term436 x) = term340.
Proof. exact (TRANS (@lem6907908 x) (@lem6908022 x)). Qed.
Lemma lem6908024 (x : int) : (term435 x) = term340.
Proof. exact (TRANS (@lem6907863 x) (@lem6908023 x)). Qed.
Lemma lem6908025 (x : int) : (term451 x) = term340.
Proof. exact (TRANS (@lem6907862 x) (@lem6908024 x)). Qed.
Lemma lem6908026 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6908027 (x : int) : (term452 x) = term399.
Proof. exact (MK_COMB (@lem6908026) (@lem6908025 x)). Qed.
Lemma lem6908028 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem6908029 (x : int) : (term449 x) = term400.
Proof. exact (MK_COMB (@lem6908027 x) (@lem6908028)). Qed.
Lemma lem6908030 (x : int) : (term189 x) = term400.
Proof. exact (TRANS (@lem6907845 x) (@lem6908029 x)). Qed.
Lemma lem6908031 : term314 = term401.
Proof. exact (fun_ext (fun x : int => @lem6908030 x)). Qed.
Lemma lem6908032 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6908033 : term329 = term402.
Proof. exact (MK_COMB (@lem6908032) (@lem6908031)). Qed.
Lemma lem6908034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908035 : term326 = term453.
Proof. exact (MK_COMB (@lem6908034) (@lem6907844)). Qed.
Lemma lem6908036 : term330 = term454.
Proof. exact (MK_COMB (@lem6908035) (@lem6908033)). Qed.
Lemma lem6908037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908038 : term310 = term455.
Proof. exact (MK_COMB (@lem6908037) (@lem6907655)). Qed.
Lemma lem6908039 : term331 = term456.
Proof. exact (MK_COMB (@lem6908038) (@lem6908036)). Qed.
Lemma lem6908040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908041 : term245 = term457.
Proof. exact (MK_COMB (@lem6908040) (@lem6907218)). Qed.
Lemma lem6908042 : term332 = term458.
Proof. exact (MK_COMB (@lem6908041) (@lem6908039)). Qed.
Lemma lem6908043 : term198 = term458.
Proof. exact (TRANS (@lem6906819) (@lem6908042)). Qed.
Lemma lem6908045 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908046 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908045 int t). Qed.
Lemma lem6908047 : term404 = term402.
Proof. exact (@lem6908046 term402). Qed.
Lemma lem6908049 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908050 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908049 int t). Qed.
Lemma lem6908051 : term402 = term400.
Proof. exact (@lem6908050 term400). Qed.
Lemma lem6908052 : term404 = term400.
Proof. exact (TRANS (@lem6908047) (@lem6908051)). Qed.
Lemma lem6908053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908054 : term405 = term461.
Proof. exact (MK_COMB (@lem6908053) (@lem6908052)). Qed.
Lemma lem6908056 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908057 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908056 int t). Qed.
Lemma lem6908058 : term404 = term402.
Proof. exact (@lem6908057 term402). Qed.
Lemma lem6908060 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908061 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908060 int t). Qed.
Lemma lem6908062 : term402 = term400.
Proof. exact (@lem6908061 term400). Qed.
Lemma lem6908063 : term404 = term400.
Proof. exact (TRANS (@lem6908058) (@lem6908062)). Qed.
Lemma lem6908064 : term406 = term462.
Proof. exact (MK_COMB (@lem6908054) (@lem6908063)). Qed.
Lemma lem6908065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908066 : term457 = term463.
Proof. exact (MK_COMB (@lem6908065) (@lem6908064)). Qed.
Lemma lem6908068 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908069 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908068 int t). Qed.
Lemma lem6908070 : term426 = term404.
Proof. exact (@lem6908069 term404). Qed.
Lemma lem6908072 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908073 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908072 int t). Qed.
Lemma lem6908074 : term404 = term402.
Proof. exact (@lem6908073 term402). Qed.
Lemma lem6908076 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908077 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908076 int t). Qed.
Lemma lem6908078 : term402 = term400.
Proof. exact (@lem6908077 term400). Qed.
Lemma lem6908079 : term404 = term400.
Proof. exact (TRANS (@lem6908074) (@lem6908078)). Qed.
Lemma lem6908080 : term426 = term400.
Proof. exact (TRANS (@lem6908070) (@lem6908079)). Qed.
Lemma lem6908081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908082 : term430 = term461.
Proof. exact (MK_COMB (@lem6908081) (@lem6908080)). Qed.
Lemma lem6908084 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908085 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908084 int t). Qed.
Lemma lem6908086 : term426 = term404.
Proof. exact (@lem6908085 term404). Qed.
Lemma lem6908088 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908089 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908088 int t). Qed.
Lemma lem6908090 : term404 = term402.
Proof. exact (@lem6908089 term402). Qed.
Lemma lem6908092 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908093 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908092 int t). Qed.
Lemma lem6908094 : term402 = term400.
Proof. exact (@lem6908093 term400). Qed.
Lemma lem6908095 : term404 = term400.
Proof. exact (TRANS (@lem6908090) (@lem6908094)). Qed.
Lemma lem6908096 : term426 = term400.
Proof. exact (TRANS (@lem6908086) (@lem6908095)). Qed.
Lemma lem6908097 : term431 = term462.
Proof. exact (MK_COMB (@lem6908082) (@lem6908096)). Qed.
Lemma lem6908098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908099 : term455 = term463.
Proof. exact (MK_COMB (@lem6908098) (@lem6908097)). Qed.
Lemma lem6908101 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908102 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908101 int t). Qed.
Lemma lem6908103 : term402 = term400.
Proof. exact (@lem6908102 term400). Qed.
Lemma lem6908104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6908105 : term453 = term461.
Proof. exact (MK_COMB (@lem6908104) (@lem6908103)). Qed.
Lemma lem6908107 {A : Type'} (t : Prop) : (term459 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6908108 (t : Prop) : (term460 t) = t.
Proof. exact (@lem6908107 int t). Qed.
Lemma lem6908109 : term402 = term400.
Proof. exact (@lem6908108 term400). Qed.
Lemma lem6908110 : term454 = term462.
Proof. exact (MK_COMB (@lem6908105) (@lem6908109)). Qed.
Lemma lem6908111 : term456 = term464.
Proof. exact (MK_COMB (@lem6908099) (@lem6908110)). Qed.
Lemma lem6908114 : term458 = term465.
Proof. exact (MK_COMB (@lem6908066) (@lem6908111)). Qed.
Lemma lem6908139 : term198 = term465.
Proof. exact (TRANS (@lem6908043) (@lem6908114)). Qed.
Lemma lem6908173 (h1 : term465) : term465.
Proof. exact (h1). Qed.
Lemma lem6908174 (h1 : term462) : term462.
Proof. exact (h1). Qed.
Lemma lem6908175 (h1 : term400) : term400.
Proof. exact (h1). Qed.
Lemma lem6908177 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6908178 : term400 = term466.
Proof. exact (@lem6908177 term375 term340). Qed.
Lemma lem6908180 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6908181 : term340 = term345.
Proof. exact (@lem6908180 term108). Qed.
Lemma lem6908183 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6908184 : term375 = term392.
Proof. exact (@lem6908183 (NUMERAL 0)). Qed.
Lemma lem6908185 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908186 : term467 = term468.
Proof. exact (MK_COMB (@lem6908185) (@lem6908184)). Qed.
Lemma lem6908187 : term466 = term469.
Proof. exact (MK_COMB (@lem6908186) (@lem6908181)). Qed.
Lemma lem6908188 : term470.
Proof. exact (@lem1980026 term375 term107 term340 term107). Qed.
Lemma lem6908190 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908191 : term377 = term378.
Proof. exact (@lem6908190 (NUMERAL 0) term108). Qed.
Lemma lem6908192 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908193 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908194 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908193 h1) (fun h1 : term378 = True => @lem6908192)). Qed.
Lemma lem6908195 : term378 = True.
Proof. exact (EQ_MP (@lem6908194) (@lem6908192)). Qed.
Lemma lem6908196 : term377 = True.
Proof. exact (TRANS (@lem6908191) (@lem6908195)). Qed.
Lemma lem6908197 : True = term377.
Proof. exact (SYM (@lem6908196)). Qed.
Lemma lem6908198 : term377.
Proof. exact (EQ_MP (@lem6908197) (@lem0)). Qed.
Lemma lem6908199 : term471.
Proof. exact (@lem6908188 (@lem6908198)). Qed.
Lemma lem6908201 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908202 : term377 = term378.
Proof. exact (@lem6908201 (NUMERAL 0) term108). Qed.
Lemma lem6908203 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908204 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908205 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908204 h1) (fun h1 : term378 = True => @lem6908203)). Qed.
Lemma lem6908206 : term378 = True.
Proof. exact (EQ_MP (@lem6908205) (@lem6908203)). Qed.
Lemma lem6908207 : term377 = True.
Proof. exact (TRANS (@lem6908202) (@lem6908206)). Qed.
Lemma lem6908208 : True = term377.
Proof. exact (SYM (@lem6908207)). Qed.
Lemma lem6908209 : term377.
Proof. exact (EQ_MP (@lem6908208) (@lem0)). Qed.
Lemma lem6908210 : term469 = term472.
Proof. exact (@lem6908199 (@lem6908209)). Qed.
Lemma lem6908212 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6908213 : term348 = term359.
Proof. exact (@lem6908212 term108 term108). Qed.
Lemma lem6908214 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6908215 : term356 = term108.
Proof. exact (EQ_MP (@lem6908214) (@lem940073)). Qed.
Lemma lem6908216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6908217 : term354 = term107.
Proof. exact (MK_COMB (@lem6908216) (@lem6908215)). Qed.
Lemma lem6908218 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6908219 : term359 = term340.
Proof. exact (MK_COMB (@lem6908218) (@lem6908217)). Qed.
Lemma lem6908220 : term348 = term340.
Proof. exact (TRANS (@lem6908213) (@lem6908219)). Qed.
Lemma lem6908222 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6908223 : term389 = term375.
Proof. exact (@lem6908222 term108). Qed.
Lemma lem6908224 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908225 : term473 = term467.
Proof. exact (MK_COMB (@lem6908224) (@lem6908223)). Qed.
Lemma lem6908226 : term472 = term466.
Proof. exact (MK_COMB (@lem6908225) (@lem6908220)). Qed.
Lemma lem6908228 (m : nat) (n : nat) : (term474 m n) = (term475 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6908229 : term466 = term476.
Proof. exact (@lem6908228 (NUMERAL 0) term108). Qed.
Lemma lem6908230 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908231 (h1 : term379 = (BIT1 0)) : (term108 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6908232 : (term379 = (BIT1 0)) = ((term108 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908231 h1) (fun h1 : (term108 = (NUMERAL 0)) = False => @lem6908230)). Qed.
Lemma lem6908233 : (term108 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6908232) (@lem6908230)). Qed.
Lemma lem6908234 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6908235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6908236 : term477 = (and True).
Proof. exact (MK_COMB (@lem6908235) (@lem6908234)). Qed.
Lemma lem6908237 : term476 = (True /\ False).
Proof. exact (MK_COMB (@lem6908236) (@lem6908233)). Qed.
Lemma lem6908239 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6908240 : term476 = False.
Proof. exact (TRANS (@lem6908237) (@lem6908239)). Qed.
Lemma lem6908241 : term466 = False.
Proof. exact (TRANS (@lem6908229) (@lem6908240)). Qed.
Lemma lem6908242 : term472 = False.
Proof. exact (TRANS (@lem6908226) (@lem6908241)). Qed.
Lemma lem6908243 : term469 = False.
Proof. exact (TRANS (@lem6908210) (@lem6908242)). Qed.
Lemma lem6908244 : term466 = False.
Proof. exact (TRANS (@lem6908187) (@lem6908243)). Qed.
Lemma lem6908245 : term400 = False.
Proof. exact (TRANS (@lem6908178) (@lem6908244)). Qed.
Lemma lem6908246 (h1 : term400) : False.
Proof. exact (EQ_MP (@lem6908245) (@lem6908175 h1)). Qed.
Lemma lem6908247 (h1 : term400) : term400.
Proof. exact (h1). Qed.
Lemma lem6908249 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6908250 : term400 = term466.
Proof. exact (@lem6908249 term375 term340). Qed.
Lemma lem6908252 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6908253 : term340 = term345.
Proof. exact (@lem6908252 term108). Qed.
Lemma lem6908255 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6908256 : term375 = term392.
Proof. exact (@lem6908255 (NUMERAL 0)). Qed.
Lemma lem6908257 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908258 : term467 = term468.
Proof. exact (MK_COMB (@lem6908257) (@lem6908256)). Qed.
Lemma lem6908259 : term466 = term469.
Proof. exact (MK_COMB (@lem6908258) (@lem6908253)). Qed.
Lemma lem6908260 : term470.
Proof. exact (@lem1980026 term375 term107 term340 term107). Qed.
Lemma lem6908262 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908263 : term377 = term378.
Proof. exact (@lem6908262 (NUMERAL 0) term108). Qed.
Lemma lem6908264 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908265 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908266 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908265 h1) (fun h1 : term378 = True => @lem6908264)). Qed.
Lemma lem6908267 : term378 = True.
Proof. exact (EQ_MP (@lem6908266) (@lem6908264)). Qed.
Lemma lem6908268 : term377 = True.
Proof. exact (TRANS (@lem6908263) (@lem6908267)). Qed.
Lemma lem6908269 : True = term377.
Proof. exact (SYM (@lem6908268)). Qed.
Lemma lem6908270 : term377.
Proof. exact (EQ_MP (@lem6908269) (@lem0)). Qed.
Lemma lem6908271 : term471.
Proof. exact (@lem6908260 (@lem6908270)). Qed.
Lemma lem6908273 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908274 : term377 = term378.
Proof. exact (@lem6908273 (NUMERAL 0) term108). Qed.
Lemma lem6908275 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908276 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908277 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908276 h1) (fun h1 : term378 = True => @lem6908275)). Qed.
Lemma lem6908278 : term378 = True.
Proof. exact (EQ_MP (@lem6908277) (@lem6908275)). Qed.
Lemma lem6908279 : term377 = True.
Proof. exact (TRANS (@lem6908274) (@lem6908278)). Qed.
Lemma lem6908280 : True = term377.
Proof. exact (SYM (@lem6908279)). Qed.
Lemma lem6908281 : term377.
Proof. exact (EQ_MP (@lem6908280) (@lem0)). Qed.
Lemma lem6908282 : term469 = term472.
Proof. exact (@lem6908271 (@lem6908281)). Qed.
Lemma lem6908284 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6908285 : term348 = term359.
Proof. exact (@lem6908284 term108 term108). Qed.
Lemma lem6908286 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6908287 : term356 = term108.
Proof. exact (EQ_MP (@lem6908286) (@lem940073)). Qed.
Lemma lem6908288 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6908289 : term354 = term107.
Proof. exact (MK_COMB (@lem6908288) (@lem6908287)). Qed.
Lemma lem6908290 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6908291 : term359 = term340.
Proof. exact (MK_COMB (@lem6908290) (@lem6908289)). Qed.
Lemma lem6908292 : term348 = term340.
Proof. exact (TRANS (@lem6908285) (@lem6908291)). Qed.
Lemma lem6908294 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6908295 : term389 = term375.
Proof. exact (@lem6908294 term108). Qed.
Lemma lem6908296 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908297 : term473 = term467.
Proof. exact (MK_COMB (@lem6908296) (@lem6908295)). Qed.
Lemma lem6908298 : term472 = term466.
Proof. exact (MK_COMB (@lem6908297) (@lem6908292)). Qed.
Lemma lem6908300 (m : nat) (n : nat) : (term474 m n) = (term475 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6908301 : term466 = term476.
Proof. exact (@lem6908300 (NUMERAL 0) term108). Qed.
Lemma lem6908302 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908303 (h1 : term379 = (BIT1 0)) : (term108 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6908304 : (term379 = (BIT1 0)) = ((term108 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908303 h1) (fun h1 : (term108 = (NUMERAL 0)) = False => @lem6908302)). Qed.
Lemma lem6908305 : (term108 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6908304) (@lem6908302)). Qed.
Lemma lem6908306 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6908307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6908308 : term477 = (and True).
Proof. exact (MK_COMB (@lem6908307) (@lem6908306)). Qed.
Lemma lem6908309 : term476 = (True /\ False).
Proof. exact (MK_COMB (@lem6908308) (@lem6908305)). Qed.
Lemma lem6908311 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6908312 : term476 = False.
Proof. exact (TRANS (@lem6908309) (@lem6908311)). Qed.
Lemma lem6908313 : term466 = False.
Proof. exact (TRANS (@lem6908301) (@lem6908312)). Qed.
Lemma lem6908314 : term472 = False.
Proof. exact (TRANS (@lem6908298) (@lem6908313)). Qed.
Lemma lem6908315 : term469 = False.
Proof. exact (TRANS (@lem6908282) (@lem6908314)). Qed.
Lemma lem6908316 : term466 = False.
Proof. exact (TRANS (@lem6908259) (@lem6908315)). Qed.
Lemma lem6908317 : term400 = False.
Proof. exact (TRANS (@lem6908250) (@lem6908316)). Qed.
Lemma lem6908318 (h1 : term400) : False.
Proof. exact (EQ_MP (@lem6908317) (@lem6908247 h1)). Qed.
Lemma lem6908319 (h1 : term462) : False.
Proof. exact (or_elim (@lem6908174 h1) (fun h0 : term400 => @lem6908246 h0) (fun h0 : term400 => @lem6908318 h0)). Qed.
Lemma lem6908320 (h1 : term464) : term464.
Proof. exact (h1). Qed.
Lemma lem6908321 (h1 : term462) : term462.
Proof. exact (h1). Qed.
Lemma lem6908322 (h1 : term400) : term400.
Proof. exact (h1). Qed.
Lemma lem6908324 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6908325 : term400 = term466.
Proof. exact (@lem6908324 term375 term340). Qed.
Lemma lem6908327 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6908328 : term340 = term345.
Proof. exact (@lem6908327 term108). Qed.
Lemma lem6908330 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6908331 : term375 = term392.
Proof. exact (@lem6908330 (NUMERAL 0)). Qed.
Lemma lem6908332 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908333 : term467 = term468.
Proof. exact (MK_COMB (@lem6908332) (@lem6908331)). Qed.
Lemma lem6908334 : term466 = term469.
Proof. exact (MK_COMB (@lem6908333) (@lem6908328)). Qed.
Lemma lem6908335 : term470.
Proof. exact (@lem1980026 term375 term107 term340 term107). Qed.
Lemma lem6908337 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908338 : term377 = term378.
Proof. exact (@lem6908337 (NUMERAL 0) term108). Qed.
Lemma lem6908339 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908340 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908341 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908340 h1) (fun h1 : term378 = True => @lem6908339)). Qed.
Lemma lem6908342 : term378 = True.
Proof. exact (EQ_MP (@lem6908341) (@lem6908339)). Qed.
Lemma lem6908343 : term377 = True.
Proof. exact (TRANS (@lem6908338) (@lem6908342)). Qed.
Lemma lem6908344 : True = term377.
Proof. exact (SYM (@lem6908343)). Qed.
Lemma lem6908345 : term377.
Proof. exact (EQ_MP (@lem6908344) (@lem0)). Qed.
Lemma lem6908346 : term471.
Proof. exact (@lem6908335 (@lem6908345)). Qed.
Lemma lem6908348 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908349 : term377 = term378.
Proof. exact (@lem6908348 (NUMERAL 0) term108). Qed.
Lemma lem6908350 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908351 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908352 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908351 h1) (fun h1 : term378 = True => @lem6908350)). Qed.
Lemma lem6908353 : term378 = True.
Proof. exact (EQ_MP (@lem6908352) (@lem6908350)). Qed.
Lemma lem6908354 : term377 = True.
Proof. exact (TRANS (@lem6908349) (@lem6908353)). Qed.
Lemma lem6908355 : True = term377.
Proof. exact (SYM (@lem6908354)). Qed.
Lemma lem6908356 : term377.
Proof. exact (EQ_MP (@lem6908355) (@lem0)). Qed.
Lemma lem6908357 : term469 = term472.
Proof. exact (@lem6908346 (@lem6908356)). Qed.
Lemma lem6908359 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6908360 : term348 = term359.
Proof. exact (@lem6908359 term108 term108). Qed.
Lemma lem6908361 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6908362 : term356 = term108.
Proof. exact (EQ_MP (@lem6908361) (@lem940073)). Qed.
Lemma lem6908363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6908364 : term354 = term107.
Proof. exact (MK_COMB (@lem6908363) (@lem6908362)). Qed.
Lemma lem6908365 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6908366 : term359 = term340.
Proof. exact (MK_COMB (@lem6908365) (@lem6908364)). Qed.
Lemma lem6908367 : term348 = term340.
Proof. exact (TRANS (@lem6908360) (@lem6908366)). Qed.
Lemma lem6908369 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6908370 : term389 = term375.
Proof. exact (@lem6908369 term108). Qed.
Lemma lem6908371 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908372 : term473 = term467.
Proof. exact (MK_COMB (@lem6908371) (@lem6908370)). Qed.
Lemma lem6908373 : term472 = term466.
Proof. exact (MK_COMB (@lem6908372) (@lem6908367)). Qed.
Lemma lem6908375 (m : nat) (n : nat) : (term474 m n) = (term475 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6908376 : term466 = term476.
Proof. exact (@lem6908375 (NUMERAL 0) term108). Qed.
Lemma lem6908377 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908378 (h1 : term379 = (BIT1 0)) : (term108 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6908379 : (term379 = (BIT1 0)) = ((term108 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908378 h1) (fun h1 : (term108 = (NUMERAL 0)) = False => @lem6908377)). Qed.
Lemma lem6908380 : (term108 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6908379) (@lem6908377)). Qed.
Lemma lem6908381 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6908382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6908383 : term477 = (and True).
Proof. exact (MK_COMB (@lem6908382) (@lem6908381)). Qed.
Lemma lem6908384 : term476 = (True /\ False).
Proof. exact (MK_COMB (@lem6908383) (@lem6908380)). Qed.
Lemma lem6908386 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6908387 : term476 = False.
Proof. exact (TRANS (@lem6908384) (@lem6908386)). Qed.
Lemma lem6908388 : term466 = False.
Proof. exact (TRANS (@lem6908376) (@lem6908387)). Qed.
Lemma lem6908389 : term472 = False.
Proof. exact (TRANS (@lem6908373) (@lem6908388)). Qed.
Lemma lem6908390 : term469 = False.
Proof. exact (TRANS (@lem6908357) (@lem6908389)). Qed.
Lemma lem6908391 : term466 = False.
Proof. exact (TRANS (@lem6908334) (@lem6908390)). Qed.
Lemma lem6908392 : term400 = False.
Proof. exact (TRANS (@lem6908325) (@lem6908391)). Qed.
Lemma lem6908393 (h1 : term400) : False.
Proof. exact (EQ_MP (@lem6908392) (@lem6908322 h1)). Qed.
Lemma lem6908394 (h1 : term400) : term400.
Proof. exact (h1). Qed.
Lemma lem6908396 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6908397 : term400 = term466.
Proof. exact (@lem6908396 term375 term340). Qed.
Lemma lem6908399 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6908400 : term340 = term345.
Proof. exact (@lem6908399 term108). Qed.
Lemma lem6908402 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6908403 : term375 = term392.
Proof. exact (@lem6908402 (NUMERAL 0)). Qed.
Lemma lem6908404 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908405 : term467 = term468.
Proof. exact (MK_COMB (@lem6908404) (@lem6908403)). Qed.
Lemma lem6908406 : term466 = term469.
Proof. exact (MK_COMB (@lem6908405) (@lem6908400)). Qed.
Lemma lem6908407 : term470.
Proof. exact (@lem1980026 term375 term107 term340 term107). Qed.
Lemma lem6908409 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908410 : term377 = term378.
Proof. exact (@lem6908409 (NUMERAL 0) term108). Qed.
Lemma lem6908411 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908412 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908413 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908412 h1) (fun h1 : term378 = True => @lem6908411)). Qed.
Lemma lem6908414 : term378 = True.
Proof. exact (EQ_MP (@lem6908413) (@lem6908411)). Qed.
Lemma lem6908415 : term377 = True.
Proof. exact (TRANS (@lem6908410) (@lem6908414)). Qed.
Lemma lem6908416 : True = term377.
Proof. exact (SYM (@lem6908415)). Qed.
Lemma lem6908417 : term377.
Proof. exact (EQ_MP (@lem6908416) (@lem0)). Qed.
Lemma lem6908418 : term471.
Proof. exact (@lem6908407 (@lem6908417)). Qed.
Lemma lem6908420 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908421 : term377 = term378.
Proof. exact (@lem6908420 (NUMERAL 0) term108). Qed.
Lemma lem6908422 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908423 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908424 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908423 h1) (fun h1 : term378 = True => @lem6908422)). Qed.
Lemma lem6908425 : term378 = True.
Proof. exact (EQ_MP (@lem6908424) (@lem6908422)). Qed.
Lemma lem6908426 : term377 = True.
Proof. exact (TRANS (@lem6908421) (@lem6908425)). Qed.
Lemma lem6908427 : True = term377.
Proof. exact (SYM (@lem6908426)). Qed.
Lemma lem6908428 : term377.
Proof. exact (EQ_MP (@lem6908427) (@lem0)). Qed.
Lemma lem6908429 : term469 = term472.
Proof. exact (@lem6908418 (@lem6908428)). Qed.
Lemma lem6908431 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6908432 : term348 = term359.
Proof. exact (@lem6908431 term108 term108). Qed.
Lemma lem6908433 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6908434 : term356 = term108.
Proof. exact (EQ_MP (@lem6908433) (@lem940073)). Qed.
Lemma lem6908435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6908436 : term354 = term107.
Proof. exact (MK_COMB (@lem6908435) (@lem6908434)). Qed.
Lemma lem6908437 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6908438 : term359 = term340.
Proof. exact (MK_COMB (@lem6908437) (@lem6908436)). Qed.
Lemma lem6908439 : term348 = term340.
Proof. exact (TRANS (@lem6908432) (@lem6908438)). Qed.
Lemma lem6908441 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6908442 : term389 = term375.
Proof. exact (@lem6908441 term108). Qed.
Lemma lem6908443 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908444 : term473 = term467.
Proof. exact (MK_COMB (@lem6908443) (@lem6908442)). Qed.
Lemma lem6908445 : term472 = term466.
Proof. exact (MK_COMB (@lem6908444) (@lem6908439)). Qed.
Lemma lem6908447 (m : nat) (n : nat) : (term474 m n) = (term475 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6908448 : term466 = term476.
Proof. exact (@lem6908447 (NUMERAL 0) term108). Qed.
Lemma lem6908449 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908450 (h1 : term379 = (BIT1 0)) : (term108 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6908451 : (term379 = (BIT1 0)) = ((term108 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908450 h1) (fun h1 : (term108 = (NUMERAL 0)) = False => @lem6908449)). Qed.
Lemma lem6908452 : (term108 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6908451) (@lem6908449)). Qed.
Lemma lem6908453 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6908454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6908455 : term477 = (and True).
Proof. exact (MK_COMB (@lem6908454) (@lem6908453)). Qed.
Lemma lem6908456 : term476 = (True /\ False).
Proof. exact (MK_COMB (@lem6908455) (@lem6908452)). Qed.
Lemma lem6908458 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6908459 : term476 = False.
Proof. exact (TRANS (@lem6908456) (@lem6908458)). Qed.
Lemma lem6908460 : term466 = False.
Proof. exact (TRANS (@lem6908448) (@lem6908459)). Qed.
Lemma lem6908461 : term472 = False.
Proof. exact (TRANS (@lem6908445) (@lem6908460)). Qed.
Lemma lem6908462 : term469 = False.
Proof. exact (TRANS (@lem6908429) (@lem6908461)). Qed.
Lemma lem6908463 : term466 = False.
Proof. exact (TRANS (@lem6908406) (@lem6908462)). Qed.
Lemma lem6908464 : term400 = False.
Proof. exact (TRANS (@lem6908397) (@lem6908463)). Qed.
Lemma lem6908465 (h1 : term400) : False.
Proof. exact (EQ_MP (@lem6908464) (@lem6908394 h1)). Qed.
Lemma lem6908466 (h1 : term462) : False.
Proof. exact (or_elim (@lem6908321 h1) (fun h0 : term400 => @lem6908393 h0) (fun h0 : term400 => @lem6908465 h0)). Qed.
Lemma lem6908467 (h1 : term462) : term462.
Proof. exact (h1). Qed.
Lemma lem6908468 (h1 : term400) : term400.
Proof. exact (h1). Qed.
Lemma lem6908470 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6908471 : term400 = term466.
Proof. exact (@lem6908470 term375 term340). Qed.
Lemma lem6908473 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6908474 : term340 = term345.
Proof. exact (@lem6908473 term108). Qed.
Lemma lem6908476 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6908477 : term375 = term392.
Proof. exact (@lem6908476 (NUMERAL 0)). Qed.
Lemma lem6908478 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908479 : term467 = term468.
Proof. exact (MK_COMB (@lem6908478) (@lem6908477)). Qed.
Lemma lem6908480 : term466 = term469.
Proof. exact (MK_COMB (@lem6908479) (@lem6908474)). Qed.
Lemma lem6908481 : term470.
Proof. exact (@lem1980026 term375 term107 term340 term107). Qed.
Lemma lem6908483 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908484 : term377 = term378.
Proof. exact (@lem6908483 (NUMERAL 0) term108). Qed.
Lemma lem6908485 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908486 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908487 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908486 h1) (fun h1 : term378 = True => @lem6908485)). Qed.
Lemma lem6908488 : term378 = True.
Proof. exact (EQ_MP (@lem6908487) (@lem6908485)). Qed.
Lemma lem6908489 : term377 = True.
Proof. exact (TRANS (@lem6908484) (@lem6908488)). Qed.
Lemma lem6908490 : True = term377.
Proof. exact (SYM (@lem6908489)). Qed.
Lemma lem6908491 : term377.
Proof. exact (EQ_MP (@lem6908490) (@lem0)). Qed.
Lemma lem6908492 : term471.
Proof. exact (@lem6908481 (@lem6908491)). Qed.
Lemma lem6908494 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908495 : term377 = term378.
Proof. exact (@lem6908494 (NUMERAL 0) term108). Qed.
Lemma lem6908496 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908497 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908498 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908497 h1) (fun h1 : term378 = True => @lem6908496)). Qed.
Lemma lem6908499 : term378 = True.
Proof. exact (EQ_MP (@lem6908498) (@lem6908496)). Qed.
Lemma lem6908500 : term377 = True.
Proof. exact (TRANS (@lem6908495) (@lem6908499)). Qed.
Lemma lem6908501 : True = term377.
Proof. exact (SYM (@lem6908500)). Qed.
Lemma lem6908502 : term377.
Proof. exact (EQ_MP (@lem6908501) (@lem0)). Qed.
Lemma lem6908503 : term469 = term472.
Proof. exact (@lem6908492 (@lem6908502)). Qed.
Lemma lem6908505 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6908506 : term348 = term359.
Proof. exact (@lem6908505 term108 term108). Qed.
Lemma lem6908507 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6908508 : term356 = term108.
Proof. exact (EQ_MP (@lem6908507) (@lem940073)). Qed.
Lemma lem6908509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6908510 : term354 = term107.
Proof. exact (MK_COMB (@lem6908509) (@lem6908508)). Qed.
Lemma lem6908511 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6908512 : term359 = term340.
Proof. exact (MK_COMB (@lem6908511) (@lem6908510)). Qed.
Lemma lem6908513 : term348 = term340.
Proof. exact (TRANS (@lem6908506) (@lem6908512)). Qed.
Lemma lem6908515 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6908516 : term389 = term375.
Proof. exact (@lem6908515 term108). Qed.
Lemma lem6908517 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908518 : term473 = term467.
Proof. exact (MK_COMB (@lem6908517) (@lem6908516)). Qed.
Lemma lem6908519 : term472 = term466.
Proof. exact (MK_COMB (@lem6908518) (@lem6908513)). Qed.
Lemma lem6908521 (m : nat) (n : nat) : (term474 m n) = (term475 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6908522 : term466 = term476.
Proof. exact (@lem6908521 (NUMERAL 0) term108). Qed.
Lemma lem6908523 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908524 (h1 : term379 = (BIT1 0)) : (term108 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6908525 : (term379 = (BIT1 0)) = ((term108 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908524 h1) (fun h1 : (term108 = (NUMERAL 0)) = False => @lem6908523)). Qed.
Lemma lem6908526 : (term108 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6908525) (@lem6908523)). Qed.
Lemma lem6908527 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6908528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6908529 : term477 = (and True).
Proof. exact (MK_COMB (@lem6908528) (@lem6908527)). Qed.
Lemma lem6908530 : term476 = (True /\ False).
Proof. exact (MK_COMB (@lem6908529) (@lem6908526)). Qed.
Lemma lem6908532 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6908533 : term476 = False.
Proof. exact (TRANS (@lem6908530) (@lem6908532)). Qed.
Lemma lem6908534 : term466 = False.
Proof. exact (TRANS (@lem6908522) (@lem6908533)). Qed.
Lemma lem6908535 : term472 = False.
Proof. exact (TRANS (@lem6908519) (@lem6908534)). Qed.
Lemma lem6908536 : term469 = False.
Proof. exact (TRANS (@lem6908503) (@lem6908535)). Qed.
Lemma lem6908537 : term466 = False.
Proof. exact (TRANS (@lem6908480) (@lem6908536)). Qed.
Lemma lem6908538 : term400 = False.
Proof. exact (TRANS (@lem6908471) (@lem6908537)). Qed.
Lemma lem6908539 (h1 : term400) : False.
Proof. exact (EQ_MP (@lem6908538) (@lem6908468 h1)). Qed.
Lemma lem6908540 (h1 : term400) : term400.
Proof. exact (h1). Qed.
Lemma lem6908542 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6908543 : term400 = term466.
Proof. exact (@lem6908542 term375 term340). Qed.
Lemma lem6908545 (x : nat) : (term343 x) = (term344 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6908546 : term340 = term345.
Proof. exact (@lem6908545 term108). Qed.
Lemma lem6908548 (x : nat) : (real_of_num x) = (term341 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6908549 : term375 = term392.
Proof. exact (@lem6908548 (NUMERAL 0)). Qed.
Lemma lem6908550 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908551 : term467 = term468.
Proof. exact (MK_COMB (@lem6908550) (@lem6908549)). Qed.
Lemma lem6908552 : term466 = term469.
Proof. exact (MK_COMB (@lem6908551) (@lem6908546)). Qed.
Lemma lem6908553 : term470.
Proof. exact (@lem1980026 term375 term107 term340 term107). Qed.
Lemma lem6908555 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908556 : term377 = term378.
Proof. exact (@lem6908555 (NUMERAL 0) term108). Qed.
Lemma lem6908557 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908558 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908559 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908558 h1) (fun h1 : term378 = True => @lem6908557)). Qed.
Lemma lem6908560 : term378 = True.
Proof. exact (EQ_MP (@lem6908559) (@lem6908557)). Qed.
Lemma lem6908561 : term377 = True.
Proof. exact (TRANS (@lem6908556) (@lem6908560)). Qed.
Lemma lem6908562 : True = term377.
Proof. exact (SYM (@lem6908561)). Qed.
Lemma lem6908563 : term377.
Proof. exact (EQ_MP (@lem6908562) (@lem0)). Qed.
Lemma lem6908564 : term471.
Proof. exact (@lem6908553 (@lem6908563)). Qed.
Lemma lem6908566 (m : nat) (n : nat) : (term376 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6908567 : term377 = term378.
Proof. exact (@lem6908566 (NUMERAL 0) term108). Qed.
Lemma lem6908568 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908569 (h1 : term379 = (BIT1 0)) : term378 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6908570 : (term379 = (BIT1 0)) = (term378 = True).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908569 h1) (fun h1 : term378 = True => @lem6908568)). Qed.
Lemma lem6908571 : term378 = True.
Proof. exact (EQ_MP (@lem6908570) (@lem6908568)). Qed.
Lemma lem6908572 : term377 = True.
Proof. exact (TRANS (@lem6908567) (@lem6908571)). Qed.
Lemma lem6908573 : True = term377.
Proof. exact (SYM (@lem6908572)). Qed.
Lemma lem6908574 : term377.
Proof. exact (EQ_MP (@lem6908573) (@lem0)). Qed.
Lemma lem6908575 : term469 = term472.
Proof. exact (@lem6908564 (@lem6908574)). Qed.
Lemma lem6908577 (m : nat) (n : nat) : (term357 m n) = (term358 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6908578 : term348 = term359.
Proof. exact (@lem6908577 term108 term108). Qed.
Lemma lem6908579 : (term355 = (BIT1 0)) = (term356 = term108).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6908580 : term356 = term108.
Proof. exact (EQ_MP (@lem6908579) (@lem940073)). Qed.
Lemma lem6908581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6908582 : term354 = term107.
Proof. exact (MK_COMB (@lem6908581) (@lem6908580)). Qed.
Lemma lem6908583 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6908584 : term359 = term340.
Proof. exact (MK_COMB (@lem6908583) (@lem6908582)). Qed.
Lemma lem6908585 : term348 = term340.
Proof. exact (TRANS (@lem6908578) (@lem6908584)). Qed.
Lemma lem6908587 (x : nat) : (term390 x) = term375.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6908588 : term389 = term375.
Proof. exact (@lem6908587 term108). Qed.
Lemma lem6908589 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6908590 : term473 = term467.
Proof. exact (MK_COMB (@lem6908589) (@lem6908588)). Qed.
Lemma lem6908591 : term472 = term466.
Proof. exact (MK_COMB (@lem6908590) (@lem6908585)). Qed.
Lemma lem6908593 (m : nat) (n : nat) : (term474 m n) = (term475 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6908594 : term466 = term476.
Proof. exact (@lem6908593 (NUMERAL 0) term108). Qed.
Lemma lem6908595 : term379 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6908596 (h1 : term379 = (BIT1 0)) : (term108 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6908597 : (term379 = (BIT1 0)) = ((term108 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term379 = (BIT1 0) => @lem6908596 h1) (fun h1 : (term108 = (NUMERAL 0)) = False => @lem6908595)). Qed.
Lemma lem6908598 : (term108 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6908597) (@lem6908595)). Qed.
Lemma lem6908599 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6908600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6908601 : term477 = (and True).
Proof. exact (MK_COMB (@lem6908600) (@lem6908599)). Qed.
Lemma lem6908602 : term476 = (True /\ False).
Proof. exact (MK_COMB (@lem6908601) (@lem6908598)). Qed.
Lemma lem6908604 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6908605 : term476 = False.
Proof. exact (TRANS (@lem6908602) (@lem6908604)). Qed.
Lemma lem6908606 : term466 = False.
Proof. exact (TRANS (@lem6908594) (@lem6908605)). Qed.
Lemma lem6908607 : term472 = False.
Proof. exact (TRANS (@lem6908591) (@lem6908606)). Qed.
Lemma lem6908608 : term469 = False.
Proof. exact (TRANS (@lem6908575) (@lem6908607)). Qed.
Lemma lem6908609 : term466 = False.
Proof. exact (TRANS (@lem6908552) (@lem6908608)). Qed.
Lemma lem6908610 : term400 = False.
Proof. exact (TRANS (@lem6908543) (@lem6908609)). Qed.
Lemma lem6908611 (h1 : term400) : False.
Proof. exact (EQ_MP (@lem6908610) (@lem6908540 h1)). Qed.
Lemma lem6908612 (h1 : term462) : False.
Proof. exact (or_elim (@lem6908467 h1) (fun h0 : term400 => @lem6908539 h0) (fun h0 : term400 => @lem6908611 h0)). Qed.
Lemma lem6908613 (h1 : term464) : False.
Proof. exact (or_elim (@lem6908320 h1) (fun h0 : term462 => @lem6908466 h0) (fun h0 : term462 => @lem6908612 h0)). Qed.
Lemma lem6908614 (h1 : term465) : False.
Proof. exact (or_elim (@lem6908173 h1) (fun h0 : term462 => @lem6908319 h0) (fun h0 : term464 => @lem6908613 h0)). Qed.
Lemma lem6908616 (h1 : term465) : term465.
Proof. exact (h1). Qed.
Lemma lem6908617 (h1 : term465) : term465 = False.
Proof. exact (prop_ext (fun h2 : term465 => @lem6908614 h1) (fun h2 : False => @lem6908616 h1)). Qed.
Lemma lem6908618 (h1 : term465) : False.
Proof. exact (EQ_MP (@lem6908617 h1) (@lem6908616 h1)). Qed.
Lemma lem6908619 (h1 : term198) : term198.
Proof. exact (h1). Qed.
Lemma lem6908620 (h1 : term198) : term465.
Proof. exact (EQ_MP (@lem6908139) (@lem6908619 h1)). Qed.
Lemma lem6908621 (h1 : term198) : term465 = False.
Proof. exact (prop_ext (fun h2 : term465 => @lem6908618 h2) (fun h2 : False => @lem6908620 h1)). Qed.
Lemma lem6908622 (h1 : term198) : False.
Proof. exact (EQ_MP (@lem6908621 h1) (@lem6908620 h1)). Qed.
Lemma lem6908623 : term478.
Proof. exact (fun h0 : term198 => @lem6908622 h0). Qed.
Lemma lem6908624 : term479.
Proof. exact (@lem1386578 term480). Qed.
Lemma lem6908627 : term480.
Proof. exact (@lem6908624 (@lem6908623)). Qed.
Lemma lem6908628 : term196 = term88.
Proof. exact (SYM (@lem6906404)). Qed.
Lemma lem6908629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6908630 : term480 = term20.
Proof. exact (MK_COMB (@lem6908629) (@lem6908628)). Qed.
Lemma lem6908631 : term20.
Proof. exact (EQ_MP (@lem6908630) (@lem6908627)). Qed.
Lemma lem6908632 : term19.
Proof. exact (EQ_MP (@lem6906007) (@lem6908631)). Qed.
Lemma lem6908633 : term19 = (term19 = True).
Proof. exact (@lem7 term19). Qed.
Lemma lem6908634 : term19 = True.
Proof. exact (EQ_MP (@lem6908633) (@lem6908632)). Qed.
Lemma lem6908635 : True = term19.
Proof. exact (SYM (@lem6908634)). Qed.
Lemma lem6908636 : term19.
Proof. exact (EQ_MP (@lem6908635) (@lem0)). Qed.
Lemma lem6908637 : @monoidal int int_mul.
Proof. exact (EQ_MP (@lem6906006) (@lem6908636)). Qed.
