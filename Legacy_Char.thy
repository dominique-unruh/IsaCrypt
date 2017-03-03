theory Legacy_Char
imports Main
begin

datatype nibble =
    Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 | Nibble6 | Nibble7
  | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD | NibbleE | NibbleF
    
datatype legacy_char = LegacyChar nibble nibble

function mk_legacy_nibble :: "nat \<Rightarrow> nibble" where
  "mk_legacy_nibble 0 = Nibble0"
| "mk_legacy_nibble (Suc 0) = Nibble1"
| "mk_legacy_nibble 2 = Nibble2"
| "mk_legacy_nibble 3 = Nibble3"
| "mk_legacy_nibble 4 = Nibble4"
| "mk_legacy_nibble 5 = Nibble5"
| "mk_legacy_nibble 6 = Nibble6"
| "mk_legacy_nibble 7 = Nibble7"
| "mk_legacy_nibble 8 = Nibble8"
| "mk_legacy_nibble 9 = Nibble9"
| "mk_legacy_nibble 10 = NibbleA"
| "mk_legacy_nibble 11 = NibbleB"
| "mk_legacy_nibble 12 = NibbleC"
| "mk_legacy_nibble 13 = NibbleD"
| "mk_legacy_nibble 14 = NibbleE"
| "mk_legacy_nibble 15 = NibbleF"
| "x \<ge> 16 \<Longrightarrow> mk_legacy_nibble x = undefined"
                      apply auto apply atomize_elim by arith
termination apply (relation "{}") by auto
  
fun unmk_legacy_nibble where
  "unmk_legacy_nibble Nibble0 = 0"
| "unmk_legacy_nibble Nibble1 = 1"
| "unmk_legacy_nibble Nibble2 = 2"
| "unmk_legacy_nibble Nibble3 = 3"
| "unmk_legacy_nibble Nibble4 = 4"
| "unmk_legacy_nibble Nibble5 = 5"
| "unmk_legacy_nibble Nibble6 = 6"
| "unmk_legacy_nibble Nibble7 = 7"
| "unmk_legacy_nibble Nibble8 = 8"
| "unmk_legacy_nibble Nibble9 = 9"
| "unmk_legacy_nibble NibbleA = 10"
| "unmk_legacy_nibble NibbleB = 11"
| "unmk_legacy_nibble NibbleC = 12"
| "unmk_legacy_nibble NibbleD = 13"
| "unmk_legacy_nibble NibbleE = 14"
| "unmk_legacy_nibble NibbleF = 15"

    
definition mk_legacy_char :: "char \<Rightarrow> legacy_char" where
  "mk_legacy_char c = LegacyChar (mk_legacy_nibble (nat_of_char c div 16))  (mk_legacy_nibble (nat_of_char c mod 16))"
  
lemma legacy_char_000: "mk_legacy_char CHR 000 = LegacyChar Nibble0 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_001: "mk_legacy_char CHR 001 = LegacyChar Nibble0 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_002: "mk_legacy_char CHR 002 = LegacyChar Nibble0 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_003: "mk_legacy_char CHR 003 = LegacyChar Nibble0 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_004: "mk_legacy_char CHR 004 = LegacyChar Nibble0 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_005: "mk_legacy_char CHR 005 = LegacyChar Nibble0 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_006: "mk_legacy_char CHR 006 = LegacyChar Nibble0 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_007: "mk_legacy_char CHR 007 = LegacyChar Nibble0 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_008: "mk_legacy_char CHR 008 = LegacyChar Nibble0 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_009: "mk_legacy_char CHR 009 = LegacyChar Nibble0 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_010: "mk_legacy_char CHR 010 = LegacyChar Nibble0 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_011: "mk_legacy_char CHR 011 = LegacyChar Nibble0 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_012: "mk_legacy_char CHR 012 = LegacyChar Nibble0 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_013: "mk_legacy_char CHR 013 = LegacyChar Nibble0 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_014: "mk_legacy_char CHR 014 = LegacyChar Nibble0 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_015: "mk_legacy_char CHR 015 = LegacyChar Nibble0 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_016: "mk_legacy_char CHR 016 = LegacyChar Nibble1 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_017: "mk_legacy_char CHR 017 = LegacyChar Nibble1 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_018: "mk_legacy_char CHR 018 = LegacyChar Nibble1 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_019: "mk_legacy_char CHR 019 = LegacyChar Nibble1 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_020: "mk_legacy_char CHR 020 = LegacyChar Nibble1 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_021: "mk_legacy_char CHR 021 = LegacyChar Nibble1 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_022: "mk_legacy_char CHR 022 = LegacyChar Nibble1 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_023: "mk_legacy_char CHR 023 = LegacyChar Nibble1 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_024: "mk_legacy_char CHR 024 = LegacyChar Nibble1 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_025: "mk_legacy_char CHR 025 = LegacyChar Nibble1 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_026: "mk_legacy_char CHR 026 = LegacyChar Nibble1 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_027: "mk_legacy_char CHR 027 = LegacyChar Nibble1 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_028: "mk_legacy_char CHR 028 = LegacyChar Nibble1 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_029: "mk_legacy_char CHR 029 = LegacyChar Nibble1 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_030: "mk_legacy_char CHR 030 = LegacyChar Nibble1 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_031: "mk_legacy_char CHR 031 = LegacyChar Nibble1 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_032: "mk_legacy_char CHR 032 = LegacyChar Nibble2 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_033: "mk_legacy_char CHR 033 = LegacyChar Nibble2 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_034: "mk_legacy_char CHR 034 = LegacyChar Nibble2 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_035: "mk_legacy_char CHR 035 = LegacyChar Nibble2 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_036: "mk_legacy_char CHR 036 = LegacyChar Nibble2 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_037: "mk_legacy_char CHR 037 = LegacyChar Nibble2 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_038: "mk_legacy_char CHR 038 = LegacyChar Nibble2 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_039: "mk_legacy_char CHR 039 = LegacyChar Nibble2 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_040: "mk_legacy_char CHR 040 = LegacyChar Nibble2 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_041: "mk_legacy_char CHR 041 = LegacyChar Nibble2 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_042: "mk_legacy_char CHR 042 = LegacyChar Nibble2 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_043: "mk_legacy_char CHR 043 = LegacyChar Nibble2 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_044: "mk_legacy_char CHR 044 = LegacyChar Nibble2 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_045: "mk_legacy_char CHR 045 = LegacyChar Nibble2 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_046: "mk_legacy_char CHR 046 = LegacyChar Nibble2 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_047: "mk_legacy_char CHR 047 = LegacyChar Nibble2 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_048: "mk_legacy_char CHR 048 = LegacyChar Nibble3 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_049: "mk_legacy_char CHR 049 = LegacyChar Nibble3 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_050: "mk_legacy_char CHR 050 = LegacyChar Nibble3 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_051: "mk_legacy_char CHR 051 = LegacyChar Nibble3 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_052: "mk_legacy_char CHR 052 = LegacyChar Nibble3 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_053: "mk_legacy_char CHR 053 = LegacyChar Nibble3 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_054: "mk_legacy_char CHR 054 = LegacyChar Nibble3 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_055: "mk_legacy_char CHR 055 = LegacyChar Nibble3 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_056: "mk_legacy_char CHR 056 = LegacyChar Nibble3 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_057: "mk_legacy_char CHR 057 = LegacyChar Nibble3 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_058: "mk_legacy_char CHR 058 = LegacyChar Nibble3 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_059: "mk_legacy_char CHR 059 = LegacyChar Nibble3 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_060: "mk_legacy_char CHR 060 = LegacyChar Nibble3 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_061: "mk_legacy_char CHR 061 = LegacyChar Nibble3 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_062: "mk_legacy_char CHR 062 = LegacyChar Nibble3 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_063: "mk_legacy_char CHR 063 = LegacyChar Nibble3 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_064: "mk_legacy_char CHR 064 = LegacyChar Nibble4 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_065: "mk_legacy_char CHR 065 = LegacyChar Nibble4 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_066: "mk_legacy_char CHR 066 = LegacyChar Nibble4 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_067: "mk_legacy_char CHR 067 = LegacyChar Nibble4 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_068: "mk_legacy_char CHR 068 = LegacyChar Nibble4 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_069: "mk_legacy_char CHR 069 = LegacyChar Nibble4 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_070: "mk_legacy_char CHR 070 = LegacyChar Nibble4 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_071: "mk_legacy_char CHR 071 = LegacyChar Nibble4 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_072: "mk_legacy_char CHR 072 = LegacyChar Nibble4 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_073: "mk_legacy_char CHR 073 = LegacyChar Nibble4 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_074: "mk_legacy_char CHR 074 = LegacyChar Nibble4 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_075: "mk_legacy_char CHR 075 = LegacyChar Nibble4 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_076: "mk_legacy_char CHR 076 = LegacyChar Nibble4 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_077: "mk_legacy_char CHR 077 = LegacyChar Nibble4 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_078: "mk_legacy_char CHR 078 = LegacyChar Nibble4 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_079: "mk_legacy_char CHR 079 = LegacyChar Nibble4 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_080: "mk_legacy_char CHR 080 = LegacyChar Nibble5 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_081: "mk_legacy_char CHR 081 = LegacyChar Nibble5 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_082: "mk_legacy_char CHR 082 = LegacyChar Nibble5 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_083: "mk_legacy_char CHR 083 = LegacyChar Nibble5 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_084: "mk_legacy_char CHR 084 = LegacyChar Nibble5 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_085: "mk_legacy_char CHR 085 = LegacyChar Nibble5 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_086: "mk_legacy_char CHR 086 = LegacyChar Nibble5 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_087: "mk_legacy_char CHR 087 = LegacyChar Nibble5 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_088: "mk_legacy_char CHR 088 = LegacyChar Nibble5 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_089: "mk_legacy_char CHR 089 = LegacyChar Nibble5 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_090: "mk_legacy_char CHR 090 = LegacyChar Nibble5 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_091: "mk_legacy_char CHR 091 = LegacyChar Nibble5 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_092: "mk_legacy_char CHR 092 = LegacyChar Nibble5 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_093: "mk_legacy_char CHR 093 = LegacyChar Nibble5 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_094: "mk_legacy_char CHR 094 = LegacyChar Nibble5 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_095: "mk_legacy_char CHR 095 = LegacyChar Nibble5 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_096: "mk_legacy_char CHR 096 = LegacyChar Nibble6 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_097: "mk_legacy_char CHR 097 = LegacyChar Nibble6 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_098: "mk_legacy_char CHR 098 = LegacyChar Nibble6 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_099: "mk_legacy_char CHR 099 = LegacyChar Nibble6 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_100: "mk_legacy_char CHR 100 = LegacyChar Nibble6 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_101: "mk_legacy_char CHR 101 = LegacyChar Nibble6 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_102: "mk_legacy_char CHR 102 = LegacyChar Nibble6 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_103: "mk_legacy_char CHR 103 = LegacyChar Nibble6 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_104: "mk_legacy_char CHR 104 = LegacyChar Nibble6 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_105: "mk_legacy_char CHR 105 = LegacyChar Nibble6 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_106: "mk_legacy_char CHR 106 = LegacyChar Nibble6 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_107: "mk_legacy_char CHR 107 = LegacyChar Nibble6 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_108: "mk_legacy_char CHR 108 = LegacyChar Nibble6 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_109: "mk_legacy_char CHR 109 = LegacyChar Nibble6 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_110: "mk_legacy_char CHR 110 = LegacyChar Nibble6 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_111: "mk_legacy_char CHR 111 = LegacyChar Nibble6 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_112: "mk_legacy_char CHR 112 = LegacyChar Nibble7 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_113: "mk_legacy_char CHR 113 = LegacyChar Nibble7 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_114: "mk_legacy_char CHR 114 = LegacyChar Nibble7 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_115: "mk_legacy_char CHR 115 = LegacyChar Nibble7 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_116: "mk_legacy_char CHR 116 = LegacyChar Nibble7 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_117: "mk_legacy_char CHR 117 = LegacyChar Nibble7 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_118: "mk_legacy_char CHR 118 = LegacyChar Nibble7 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_119: "mk_legacy_char CHR 119 = LegacyChar Nibble7 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_120: "mk_legacy_char CHR 120 = LegacyChar Nibble7 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_121: "mk_legacy_char CHR 121 = LegacyChar Nibble7 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_122: "mk_legacy_char CHR 122 = LegacyChar Nibble7 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_123: "mk_legacy_char CHR 123 = LegacyChar Nibble7 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_124: "mk_legacy_char CHR 124 = LegacyChar Nibble7 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_125: "mk_legacy_char CHR 125 = LegacyChar Nibble7 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_126: "mk_legacy_char CHR 126 = LegacyChar Nibble7 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_127: "mk_legacy_char CHR 127 = LegacyChar Nibble7 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_128: "mk_legacy_char CHR 128 = LegacyChar Nibble8 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_129: "mk_legacy_char CHR 129 = LegacyChar Nibble8 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_130: "mk_legacy_char CHR 130 = LegacyChar Nibble8 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_131: "mk_legacy_char CHR 131 = LegacyChar Nibble8 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_132: "mk_legacy_char CHR 132 = LegacyChar Nibble8 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_133: "mk_legacy_char CHR 133 = LegacyChar Nibble8 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_134: "mk_legacy_char CHR 134 = LegacyChar Nibble8 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_135: "mk_legacy_char CHR 135 = LegacyChar Nibble8 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_136: "mk_legacy_char CHR 136 = LegacyChar Nibble8 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_137: "mk_legacy_char CHR 137 = LegacyChar Nibble8 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_138: "mk_legacy_char CHR 138 = LegacyChar Nibble8 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_139: "mk_legacy_char CHR 139 = LegacyChar Nibble8 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_140: "mk_legacy_char CHR 140 = LegacyChar Nibble8 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_141: "mk_legacy_char CHR 141 = LegacyChar Nibble8 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_142: "mk_legacy_char CHR 142 = LegacyChar Nibble8 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_143: "mk_legacy_char CHR 143 = LegacyChar Nibble8 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_144: "mk_legacy_char CHR 144 = LegacyChar Nibble9 Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_145: "mk_legacy_char CHR 145 = LegacyChar Nibble9 Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_146: "mk_legacy_char CHR 146 = LegacyChar Nibble9 Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_147: "mk_legacy_char CHR 147 = LegacyChar Nibble9 Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_148: "mk_legacy_char CHR 148 = LegacyChar Nibble9 Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_149: "mk_legacy_char CHR 149 = LegacyChar Nibble9 Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_150: "mk_legacy_char CHR 150 = LegacyChar Nibble9 Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_151: "mk_legacy_char CHR 151 = LegacyChar Nibble9 Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_152: "mk_legacy_char CHR 152 = LegacyChar Nibble9 Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_153: "mk_legacy_char CHR 153 = LegacyChar Nibble9 Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_154: "mk_legacy_char CHR 154 = LegacyChar Nibble9 NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_155: "mk_legacy_char CHR 155 = LegacyChar Nibble9 NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_156: "mk_legacy_char CHR 156 = LegacyChar Nibble9 NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_157: "mk_legacy_char CHR 157 = LegacyChar Nibble9 NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_158: "mk_legacy_char CHR 158 = LegacyChar Nibble9 NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_159: "mk_legacy_char CHR 159 = LegacyChar Nibble9 NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_160: "mk_legacy_char CHR 160 = LegacyChar NibbleA Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_161: "mk_legacy_char CHR 161 = LegacyChar NibbleA Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_162: "mk_legacy_char CHR 162 = LegacyChar NibbleA Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_163: "mk_legacy_char CHR 163 = LegacyChar NibbleA Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_164: "mk_legacy_char CHR 164 = LegacyChar NibbleA Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_165: "mk_legacy_char CHR 165 = LegacyChar NibbleA Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_166: "mk_legacy_char CHR 166 = LegacyChar NibbleA Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_167: "mk_legacy_char CHR 167 = LegacyChar NibbleA Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_168: "mk_legacy_char CHR 168 = LegacyChar NibbleA Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_169: "mk_legacy_char CHR 169 = LegacyChar NibbleA Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_170: "mk_legacy_char CHR 170 = LegacyChar NibbleA NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_171: "mk_legacy_char CHR 171 = LegacyChar NibbleA NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_172: "mk_legacy_char CHR 172 = LegacyChar NibbleA NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_173: "mk_legacy_char CHR 173 = LegacyChar NibbleA NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_174: "mk_legacy_char CHR 174 = LegacyChar NibbleA NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_175: "mk_legacy_char CHR 175 = LegacyChar NibbleA NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_176: "mk_legacy_char CHR 176 = LegacyChar NibbleB Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_177: "mk_legacy_char CHR 177 = LegacyChar NibbleB Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_178: "mk_legacy_char CHR 178 = LegacyChar NibbleB Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_179: "mk_legacy_char CHR 179 = LegacyChar NibbleB Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_180: "mk_legacy_char CHR 180 = LegacyChar NibbleB Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_181: "mk_legacy_char CHR 181 = LegacyChar NibbleB Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_182: "mk_legacy_char CHR 182 = LegacyChar NibbleB Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_183: "mk_legacy_char CHR 183 = LegacyChar NibbleB Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_184: "mk_legacy_char CHR 184 = LegacyChar NibbleB Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_185: "mk_legacy_char CHR 185 = LegacyChar NibbleB Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_186: "mk_legacy_char CHR 186 = LegacyChar NibbleB NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_187: "mk_legacy_char CHR 187 = LegacyChar NibbleB NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_188: "mk_legacy_char CHR 188 = LegacyChar NibbleB NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_189: "mk_legacy_char CHR 189 = LegacyChar NibbleB NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_190: "mk_legacy_char CHR 190 = LegacyChar NibbleB NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_191: "mk_legacy_char CHR 191 = LegacyChar NibbleB NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_192: "mk_legacy_char CHR 192 = LegacyChar NibbleC Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_193: "mk_legacy_char CHR 193 = LegacyChar NibbleC Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_194: "mk_legacy_char CHR 194 = LegacyChar NibbleC Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_195: "mk_legacy_char CHR 195 = LegacyChar NibbleC Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_196: "mk_legacy_char CHR 196 = LegacyChar NibbleC Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_197: "mk_legacy_char CHR 197 = LegacyChar NibbleC Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_198: "mk_legacy_char CHR 198 = LegacyChar NibbleC Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_199: "mk_legacy_char CHR 199 = LegacyChar NibbleC Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_200: "mk_legacy_char CHR 200 = LegacyChar NibbleC Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_201: "mk_legacy_char CHR 201 = LegacyChar NibbleC Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_202: "mk_legacy_char CHR 202 = LegacyChar NibbleC NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_203: "mk_legacy_char CHR 203 = LegacyChar NibbleC NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_204: "mk_legacy_char CHR 204 = LegacyChar NibbleC NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_205: "mk_legacy_char CHR 205 = LegacyChar NibbleC NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_206: "mk_legacy_char CHR 206 = LegacyChar NibbleC NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_207: "mk_legacy_char CHR 207 = LegacyChar NibbleC NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_208: "mk_legacy_char CHR 208 = LegacyChar NibbleD Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_209: "mk_legacy_char CHR 209 = LegacyChar NibbleD Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_210: "mk_legacy_char CHR 210 = LegacyChar NibbleD Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_211: "mk_legacy_char CHR 211 = LegacyChar NibbleD Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_212: "mk_legacy_char CHR 212 = LegacyChar NibbleD Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_213: "mk_legacy_char CHR 213 = LegacyChar NibbleD Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_214: "mk_legacy_char CHR 214 = LegacyChar NibbleD Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_215: "mk_legacy_char CHR 215 = LegacyChar NibbleD Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_216: "mk_legacy_char CHR 216 = LegacyChar NibbleD Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_217: "mk_legacy_char CHR 217 = LegacyChar NibbleD Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_218: "mk_legacy_char CHR 218 = LegacyChar NibbleD NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_219: "mk_legacy_char CHR 219 = LegacyChar NibbleD NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_220: "mk_legacy_char CHR 220 = LegacyChar NibbleD NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_221: "mk_legacy_char CHR 221 = LegacyChar NibbleD NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_222: "mk_legacy_char CHR 222 = LegacyChar NibbleD NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_223: "mk_legacy_char CHR 223 = LegacyChar NibbleD NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_224: "mk_legacy_char CHR 224 = LegacyChar NibbleE Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_225: "mk_legacy_char CHR 225 = LegacyChar NibbleE Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_226: "mk_legacy_char CHR 226 = LegacyChar NibbleE Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_227: "mk_legacy_char CHR 227 = LegacyChar NibbleE Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_228: "mk_legacy_char CHR 228 = LegacyChar NibbleE Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_229: "mk_legacy_char CHR 229 = LegacyChar NibbleE Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_230: "mk_legacy_char CHR 230 = LegacyChar NibbleE Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_231: "mk_legacy_char CHR 231 = LegacyChar NibbleE Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_232: "mk_legacy_char CHR 232 = LegacyChar NibbleE Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_233: "mk_legacy_char CHR 233 = LegacyChar NibbleE Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_234: "mk_legacy_char CHR 234 = LegacyChar NibbleE NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_235: "mk_legacy_char CHR 235 = LegacyChar NibbleE NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_236: "mk_legacy_char CHR 236 = LegacyChar NibbleE NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_237: "mk_legacy_char CHR 237 = LegacyChar NibbleE NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_238: "mk_legacy_char CHR 238 = LegacyChar NibbleE NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_239: "mk_legacy_char CHR 239 = LegacyChar NibbleE NibbleF" by (simp add: mk_legacy_char_def)
lemma legacy_char_240: "mk_legacy_char CHR 240 = LegacyChar NibbleF Nibble0" by (simp add: mk_legacy_char_def)
lemma legacy_char_241: "mk_legacy_char CHR 241 = LegacyChar NibbleF Nibble1" by (simp add: mk_legacy_char_def)
lemma legacy_char_242: "mk_legacy_char CHR 242 = LegacyChar NibbleF Nibble2" by (simp add: mk_legacy_char_def)
lemma legacy_char_243: "mk_legacy_char CHR 243 = LegacyChar NibbleF Nibble3" by (simp add: mk_legacy_char_def)
lemma legacy_char_244: "mk_legacy_char CHR 244 = LegacyChar NibbleF Nibble4" by (simp add: mk_legacy_char_def)
lemma legacy_char_245: "mk_legacy_char CHR 245 = LegacyChar NibbleF Nibble5" by (simp add: mk_legacy_char_def)
lemma legacy_char_246: "mk_legacy_char CHR 246 = LegacyChar NibbleF Nibble6" by (simp add: mk_legacy_char_def)
lemma legacy_char_247: "mk_legacy_char CHR 247 = LegacyChar NibbleF Nibble7" by (simp add: mk_legacy_char_def)
lemma legacy_char_248: "mk_legacy_char CHR 248 = LegacyChar NibbleF Nibble8" by (simp add: mk_legacy_char_def)
lemma legacy_char_249: "mk_legacy_char CHR 249 = LegacyChar NibbleF Nibble9" by (simp add: mk_legacy_char_def)
lemma legacy_char_250: "mk_legacy_char CHR 250 = LegacyChar NibbleF NibbleA" by (simp add: mk_legacy_char_def)
lemma legacy_char_251: "mk_legacy_char CHR 251 = LegacyChar NibbleF NibbleB" by (simp add: mk_legacy_char_def)
lemma legacy_char_252: "mk_legacy_char CHR 252 = LegacyChar NibbleF NibbleC" by (simp add: mk_legacy_char_def)
lemma legacy_char_253: "mk_legacy_char CHR 253 = LegacyChar NibbleF NibbleD" by (simp add: mk_legacy_char_def)
lemma legacy_char_254: "mk_legacy_char CHR 254 = LegacyChar NibbleF NibbleE" by (simp add: mk_legacy_char_def)
lemma legacy_char_255: "mk_legacy_char CHR 255 = LegacyChar NibbleF NibbleF" by (simp add: mk_legacy_char_def)

lemmas legacy_char_simps = legacy_char_000 legacy_char_001 legacy_char_002 legacy_char_003 legacy_char_004 legacy_char_005 legacy_char_006 legacy_char_007 legacy_char_008 legacy_char_009 legacy_char_010 legacy_char_011 legacy_char_012 legacy_char_013 legacy_char_014 legacy_char_015 legacy_char_016 legacy_char_017 legacy_char_018 legacy_char_019 legacy_char_020 legacy_char_021 legacy_char_022 legacy_char_023 legacy_char_024 legacy_char_025 legacy_char_026 legacy_char_027 legacy_char_028 legacy_char_029 legacy_char_030 legacy_char_031 legacy_char_032 legacy_char_033 legacy_char_034 legacy_char_035 legacy_char_036 legacy_char_037 legacy_char_038 legacy_char_039 legacy_char_040 legacy_char_041 legacy_char_042 legacy_char_043 legacy_char_044 legacy_char_045 legacy_char_046 legacy_char_047 legacy_char_048 legacy_char_049 legacy_char_050 legacy_char_051 legacy_char_052 legacy_char_053 legacy_char_054 legacy_char_055 legacy_char_056 legacy_char_057 legacy_char_058 legacy_char_059 legacy_char_060 legacy_char_061 legacy_char_062 legacy_char_063 legacy_char_064 legacy_char_065 legacy_char_066 legacy_char_067 legacy_char_068 legacy_char_069 legacy_char_070 legacy_char_071 legacy_char_072 legacy_char_073 legacy_char_074 legacy_char_075 legacy_char_076 legacy_char_077 legacy_char_078 legacy_char_079 legacy_char_080 legacy_char_081 legacy_char_082 legacy_char_083 legacy_char_084 legacy_char_085 legacy_char_086 legacy_char_087 legacy_char_088 legacy_char_089 legacy_char_090 legacy_char_091 legacy_char_092 legacy_char_093 legacy_char_094 legacy_char_095 legacy_char_096 legacy_char_097 legacy_char_098 legacy_char_099 legacy_char_100 legacy_char_101 legacy_char_102 legacy_char_103 legacy_char_104 legacy_char_105 legacy_char_106 legacy_char_107 legacy_char_108 legacy_char_109 legacy_char_110 legacy_char_111 legacy_char_112 legacy_char_113 legacy_char_114 legacy_char_115 legacy_char_116 legacy_char_117 legacy_char_118 legacy_char_119 legacy_char_120 legacy_char_121 legacy_char_122 legacy_char_123 legacy_char_124 legacy_char_125 legacy_char_126 legacy_char_127 legacy_char_128 legacy_char_129 legacy_char_130 legacy_char_131 legacy_char_132 legacy_char_133 legacy_char_134 legacy_char_135 legacy_char_136 legacy_char_137 legacy_char_138 legacy_char_139 legacy_char_140 legacy_char_141 legacy_char_142 legacy_char_143 legacy_char_144 legacy_char_145 legacy_char_146 legacy_char_147 legacy_char_148 legacy_char_149 legacy_char_150 legacy_char_151 legacy_char_152 legacy_char_153 legacy_char_154 legacy_char_155 legacy_char_156 legacy_char_157 legacy_char_158 legacy_char_159 legacy_char_160 legacy_char_161 legacy_char_162 legacy_char_163 legacy_char_164 legacy_char_165 legacy_char_166 legacy_char_167 legacy_char_168 legacy_char_169 legacy_char_170 legacy_char_171 legacy_char_172 legacy_char_173 legacy_char_174 legacy_char_175 legacy_char_176 legacy_char_177 legacy_char_178 legacy_char_179 legacy_char_180 legacy_char_181 legacy_char_182 legacy_char_183 legacy_char_184 legacy_char_185 legacy_char_186 legacy_char_187 legacy_char_188 legacy_char_189 legacy_char_190 legacy_char_191 legacy_char_192 legacy_char_193 legacy_char_194 legacy_char_195 legacy_char_196 legacy_char_197 legacy_char_198 legacy_char_199 legacy_char_200 legacy_char_201 legacy_char_202 legacy_char_203 legacy_char_204 legacy_char_205 legacy_char_206 legacy_char_207 legacy_char_208 legacy_char_209 legacy_char_210 legacy_char_211 legacy_char_212 legacy_char_213 legacy_char_214 legacy_char_215 legacy_char_216 legacy_char_217 legacy_char_218 legacy_char_219 legacy_char_220 legacy_char_221 legacy_char_222 legacy_char_223 legacy_char_224 legacy_char_225 legacy_char_226 legacy_char_227 legacy_char_228 legacy_char_229 legacy_char_230 legacy_char_231 legacy_char_232 legacy_char_233 legacy_char_234 legacy_char_235 legacy_char_236 legacy_char_237 legacy_char_238 legacy_char_239 legacy_char_240 legacy_char_241 legacy_char_242 legacy_char_243 legacy_char_244 legacy_char_245 legacy_char_246 legacy_char_247 legacy_char_248 legacy_char_249 legacy_char_250 legacy_char_251 legacy_char_252 legacy_char_253 legacy_char_254 legacy_char_255

lemma unmk_legacy_nibble: 
  assumes "x < 16" 
  shows "unmk_legacy_nibble (mk_legacy_nibble x) = x" 
proof -
  consider "x=0" | "x=1" | "x=2" | "x=3" | "x=4" | "x=5" | "x=6" | "x=7" | "x=8" | "x=9" | "x=10" | "x=11" | "x=12" | "x=13" | "x=14" | "x=15"
    apply atomize_elim using `x<16` by arith
  thus ?thesis apply cases by simp_all
qed
  
lemma mk_legacy_nibble_inj:
  assumes "x < 16" and "y < 16" 
  shows "mk_legacy_nibble x = mk_legacy_nibble y \<longleftrightarrow> x=y"
  apply rule
   apply (subst unmk_legacy_nibble[OF `x<16`, symmetric])
   apply (subst unmk_legacy_nibble[OF `y<16`, symmetric])
  by auto

  
lemma mk_legacy_char_inj: "x = y \<longleftrightarrow> mk_legacy_char x = mk_legacy_char y" 
proof -
  define a b where "a = nat_of_char x" and "b = nat_of_char y"
  have a: "a<256" by (simp add: a_def)
  hence adiv16: "a div 16 < 16" by arith
  have amod16: "a mod 16 < 16" by arith
  have b: "b<256" by (simp add: b_def)
  hence bdiv16: "b div 16 < 16" by arith 
  have bmod16: "b mod 16 < 16" by arith
  have "(a = b) =
    (LegacyChar (mk_legacy_nibble (a div 16)) (mk_legacy_nibble (a mod 16)) =
     LegacyChar (mk_legacy_nibble (b div 16)) (mk_legacy_nibble (b mod 16)))"
    apply simp
    apply (subst mk_legacy_nibble_inj[OF adiv16 bdiv16])
    apply (subst mk_legacy_nibble_inj[OF amod16 bmod16])
    apply rule
     apply simp
    apply (subst mult_div_mod_eq[where a=a and b=16, symmetric])
    apply (subst mult_div_mod_eq[where a=b and b=16, symmetric])
    by arith
  thus ?thesis
    unfolding mk_legacy_char_def nat_of_char_eq_iff[symmetric] a_def[symmetric] b_def[symmetric] 
    by assumption
qed
  
lemma "CHR ''y'' \<noteq> CHR ''z''" 
  using[[simp_trace_new]]
  by (simp only: List.list.inject mk_legacy_char_inj legacy_char.inject nibble.distinct legacy_char_simps HOL.simp_thms)
    

end
