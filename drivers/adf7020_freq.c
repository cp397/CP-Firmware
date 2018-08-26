/*******************************************************************************
* adf7020.c
*
* By: Kenji Yamamoto
*     BluePlasma Engineering LLC
*
* Look up table for channel frequencies.
*******************************************************************************/

#include "../std.h"

/* Driver includes */
#include "adf7020.h"

/***************************************************************************//**
 * \brief Look up table for channel frequencies
 *
 * This table contains the ADF7020 register settings for producing the TX and RX
 * frequencies for each channel.
 *
 * Column 0 contains the settings for TX, Column 1 contains the settings for RX
 * which is 200 kHz below the TX frequency.
 ******************************************************************************/
const uint32 g_ucaADF7020_ChannelFrequencyLUT[ADF7020_MAX_CHANNEL][2] =
{
  { 0x028C7D10, 0x028C5800 }, /**< Chan = 000, TX = 902.000138, RX = 901.800000, DIFF = 0.200137 */
  { 0x028C8F90, 0x028C6A80 }, /**< Chan = 001, TX = 902.100038, RX = 901.899900, DIFF = 0.200138 */
  { 0x028CA210, 0x028C7D00 }, /**< Chan = 002, TX = 902.199938, RX = 901.999800, DIFF = 0.200137 */
  { 0x028CB490, 0x028C8F80 }, /**< Chan = 003, TX = 902.299838, RX = 902.099700, DIFF = 0.200137 */
  { 0x028CC710, 0x028CA200 }, /**< Chan = 004, TX = 902.399738, RX = 902.199600, DIFF = 0.200137 */
  { 0x028CD990, 0x028CB480 }, /**< Chan = 005, TX = 902.499638, RX = 902.299500, DIFF = 0.200137 */
  { 0x028CEC10, 0x028CC700 }, /**< Chan = 006, TX = 902.599537, RX = 902.399400, DIFF = 0.200137 */
  { 0x028CFE90, 0x028CD980 }, /**< Chan = 007, TX = 902.699438, RX = 902.499300, DIFF = 0.200137 */
  { 0x028D1110, 0x028CEC00 }, /**< Chan = 008, TX = 902.799338, RX = 902.599200, DIFF = 0.200138 */
  { 0x028D2390, 0x028CFE80 }, /**< Chan = 009, TX = 902.899238, RX = 902.699100, DIFF = 0.200137 */
  { 0x028D3610, 0x028D1100 }, /**< Chan = 010, TX = 902.999138, RX = 902.799000, DIFF = 0.200137 */
  { 0x028D4890, 0x028D2380 }, /**< Chan = 011, TX = 903.099038, RX = 902.898900, DIFF = 0.200137 */
  { 0x028D5B10, 0x028D3600 }, /**< Chan = 012, TX = 903.198938, RX = 902.998800, DIFF = 0.200137 */
  { 0x028D6D90, 0x028D4880 }, /**< Chan = 013, TX = 903.298838, RX = 903.098700, DIFF = 0.200138 */
  { 0x028D8010, 0x028D5B00 }, /**< Chan = 014, TX = 903.398738, RX = 903.198600, DIFF = 0.200137 */
  { 0x028D9290, 0x028D6D80 }, /**< Chan = 015, TX = 903.498638, RX = 903.298500, DIFF = 0.200137 */
  { 0x028DA510, 0x028D8000 }, /**< Chan = 016, TX = 903.598538, RX = 903.398400, DIFF = 0.200137 */
  { 0x028DB790, 0x028D9280 }, /**< Chan = 017, TX = 903.698438, RX = 903.498300, DIFF = 0.200137 */
  { 0x028DCA10, 0x028DA500 }, /**< Chan = 018, TX = 903.798338, RX = 903.598200, DIFF = 0.200137 */
  { 0x028DDC90, 0x028DB780 }, /**< Chan = 019, TX = 903.898238, RX = 903.698100, DIFF = 0.200137 */
  { 0x028DEF10, 0x028DCA00 }, /**< Chan = 020, TX = 903.998138, RX = 903.798000, DIFF = 0.200138 */
  { 0x028E0190, 0x028DDC80 }, /**< Chan = 021, TX = 904.098038, RX = 903.897900, DIFF = 0.200137 */
  { 0x028E1410, 0x028DEF00 }, /**< Chan = 022, TX = 904.197938, RX = 903.997800, DIFF = 0.200137 */
  { 0x028E2690, 0x028E0180 }, /**< Chan = 023, TX = 904.297838, RX = 904.097700, DIFF = 0.200137 */
  { 0x028E3910, 0x028E1400 }, /**< Chan = 024, TX = 904.397738, RX = 904.197600, DIFF = 0.200137 */
  { 0x028E4B90, 0x028E2680 }, /**< Chan = 025, TX = 904.497637, RX = 904.297500, DIFF = 0.200137 */
  { 0x028E5E10, 0x028E3900 }, /**< Chan = 026, TX = 904.597538, RX = 904.397400, DIFF = 0.200137 */
  { 0x028E7090, 0x028E4B80 }, /**< Chan = 027, TX = 904.697438, RX = 904.497300, DIFF = 0.200138 */
  { 0x028E8310, 0x028E5E00 }, /**< Chan = 028, TX = 904.797338, RX = 904.597200, DIFF = 0.200137 */
  { 0x028E9590, 0x028E7080 }, /**< Chan = 029, TX = 904.897238, RX = 904.697100, DIFF = 0.200137 */
  { 0x028EA810, 0x028E8300 }, /**< Chan = 030, TX = 904.997138, RX = 904.797000, DIFF = 0.200137 */
  { 0x028EBA90, 0x028E9580 }, /**< Chan = 031, TX = 905.097038, RX = 904.896900, DIFF = 0.200137 */
  { 0x028ECD10, 0x028EA800 }, /**< Chan = 032, TX = 905.196938, RX = 904.996800, DIFF = 0.200138 */
  { 0x028EDF90, 0x028EBA80 }, /**< Chan = 033, TX = 905.296838, RX = 905.096700, DIFF = 0.200137 */
  { 0x028EF210, 0x028ECD00 }, /**< Chan = 034, TX = 905.396738, RX = 905.196600, DIFF = 0.200137 */
  { 0x028F0490, 0x028EDF80 }, /**< Chan = 035, TX = 905.496638, RX = 905.296500, DIFF = 0.200137 */
  { 0x028F1710, 0x028EF200 }, /**< Chan = 036, TX = 905.596538, RX = 905.396400, DIFF = 0.200137 */
  { 0x028F2990, 0x028F0480 }, /**< Chan = 037, TX = 905.696438, RX = 905.496300, DIFF = 0.200137 */
  { 0x028F3C10, 0x028F1700 }, /**< Chan = 038, TX = 905.796338, RX = 905.596200, DIFF = 0.200137 */
  { 0x028F4E90, 0x028F2980 }, /**< Chan = 039, TX = 905.896238, RX = 905.696100, DIFF = 0.200138 */
  { 0x028F6110, 0x028F3C00 }, /**< Chan = 040, TX = 905.996138, RX = 905.796000, DIFF = 0.200137 */
  { 0x028F7390, 0x028F4E80 }, /**< Chan = 041, TX = 906.096038, RX = 905.895900, DIFF = 0.200137 */
  { 0x028F8610, 0x028F6100 }, /**< Chan = 042, TX = 906.195938, RX = 905.995800, DIFF = 0.200137 */
  { 0x028F9890, 0x028F7380 }, /**< Chan = 043, TX = 906.295838, RX = 906.095700, DIFF = 0.200137 */
  { 0x028FAB10, 0x028F8600 }, /**< Chan = 044, TX = 906.395737, RX = 906.195600, DIFF = 0.200137 */
  { 0x028FBD90, 0x028F9880 }, /**< Chan = 045, TX = 906.495638, RX = 906.295500, DIFF = 0.200137 */
  { 0x028FD010, 0x028FAB00 }, /**< Chan = 046, TX = 906.595538, RX = 906.395400, DIFF = 0.200138 */
  { 0x028FE290, 0x028FBD80 }, /**< Chan = 047, TX = 906.695438, RX = 906.495300, DIFF = 0.200137 */
  { 0x028FF510, 0x028FD000 }, /**< Chan = 048, TX = 906.795338, RX = 906.595200, DIFF = 0.200137 */
  { 0x02900790, 0x028FE280 }, /**< Chan = 049, TX = 906.895238, RX = 906.695100, DIFF = 0.200137 */
  { 0x02901A10, 0x028FF500 }, /**< Chan = 050, TX = 906.995138, RX = 906.795000, DIFF = 0.200137 */
  { 0x02902C90, 0x02900780 }, /**< Chan = 051, TX = 907.095038, RX = 906.894900, DIFF = 0.200138 */
  { 0x02903F10, 0x02901A00 }, /**< Chan = 052, TX = 907.194938, RX = 906.994800, DIFF = 0.200137 */
  { 0x02905190, 0x02902C80 }, /**< Chan = 053, TX = 907.294838, RX = 907.094700, DIFF = 0.200137 */
  { 0x02906410, 0x02903F00 }, /**< Chan = 054, TX = 907.394738, RX = 907.194600, DIFF = 0.200137 */
  { 0x02907690, 0x02905180 }, /**< Chan = 055, TX = 907.494638, RX = 907.294500, DIFF = 0.200137 */
  { 0x02908910, 0x02906400 }, /**< Chan = 056, TX = 907.594538, RX = 907.394400, DIFF = 0.200137 */
  { 0x02909B90, 0x02907680 }, /**< Chan = 057, TX = 907.694438, RX = 907.494300, DIFF = 0.200137 */
  { 0x0290AE10, 0x02908900 }, /**< Chan = 058, TX = 907.794338, RX = 907.594200, DIFF = 0.200138 */
  { 0x0290C090, 0x02909B80 }, /**< Chan = 059, TX = 907.894238, RX = 907.694100, DIFF = 0.200137 */
  { 0x0290D310, 0x0290AE00 }, /**< Chan = 060, TX = 907.994138, RX = 907.794000, DIFF = 0.200137 */
  { 0x0290E590, 0x0290C080 }, /**< Chan = 061, TX = 908.094038, RX = 907.893900, DIFF = 0.200137 */
  { 0x0290F810, 0x0290D300 }, /**< Chan = 062, TX = 908.193938, RX = 907.993800, DIFF = 0.200137 */
  { 0x02910A90, 0x0290E580 }, /**< Chan = 063, TX = 908.293837, RX = 908.093700, DIFF = 0.200137 */
  { 0x02911D10, 0x0290F800 }, /**< Chan = 064, TX = 908.393738, RX = 908.193600, DIFF = 0.200137 */
  { 0x02912F90, 0x02910A80 }, /**< Chan = 065, TX = 908.493638, RX = 908.293500, DIFF = 0.200138 */
  { 0x02914210, 0x02911D00 }, /**< Chan = 066, TX = 908.593538, RX = 908.393400, DIFF = 0.200137 */
  { 0x02915490, 0x02912F80 }, /**< Chan = 067, TX = 908.693438, RX = 908.493300, DIFF = 0.200137 */
  { 0x02916710, 0x02914200 }, /**< Chan = 068, TX = 908.793338, RX = 908.593200, DIFF = 0.200137 */
  { 0x02917990, 0x02915480 }, /**< Chan = 069, TX = 908.893238, RX = 908.693100, DIFF = 0.200137 */
  { 0x02918C10, 0x02916700 }, /**< Chan = 070, TX = 908.993138, RX = 908.793000, DIFF = 0.200138 */
  { 0x02919E90, 0x02917980 }, /**< Chan = 071, TX = 909.093038, RX = 908.892900, DIFF = 0.200137 */
  { 0x0291B110, 0x02918C00 }, /**< Chan = 072, TX = 909.192938, RX = 908.992800, DIFF = 0.200137 */
  { 0x0291C390, 0x02919E80 }, /**< Chan = 073, TX = 909.292838, RX = 909.092700, DIFF = 0.200137 */
  { 0x0291D610, 0x0291B100 }, /**< Chan = 074, TX = 909.392738, RX = 909.192600, DIFF = 0.200137 */
  { 0x0291E890, 0x0291C380 }, /**< Chan = 075, TX = 909.492638, RX = 909.292500, DIFF = 0.200137 */
  { 0x0291FB10, 0x0291D600 }, /**< Chan = 076, TX = 909.592538, RX = 909.392400, DIFF = 0.200137 */
  { 0x02920D90, 0x0291E880 }, /**< Chan = 077, TX = 909.692438, RX = 909.492300, DIFF = 0.200138 */
  { 0x02922010, 0x0291FB00 }, /**< Chan = 078, TX = 909.792338, RX = 909.592200, DIFF = 0.200137 */
  { 0x02923290, 0x02920D80 }, /**< Chan = 079, TX = 909.892238, RX = 909.692100, DIFF = 0.200137 */
  { 0x02924510, 0x02922000 }, /**< Chan = 080, TX = 909.992138, RX = 909.792000, DIFF = 0.200137 */
  { 0x02925790, 0x02923280 }, /**< Chan = 081, TX = 910.092038, RX = 909.891900, DIFF = 0.200137 */
  { 0x02926A10, 0x02924500 }, /**< Chan = 082, TX = 910.191937, RX = 909.991800, DIFF = 0.200137 */
  { 0x02927C90, 0x02925780 }, /**< Chan = 083, TX = 910.291838, RX = 910.091700, DIFF = 0.200137 */
  { 0x02928F10, 0x02926A00 }, /**< Chan = 084, TX = 910.391738, RX = 910.191600, DIFF = 0.200138 */
  { 0x0292A190, 0x02927C80 }, /**< Chan = 085, TX = 910.491638, RX = 910.291500, DIFF = 0.200137 */
  { 0x0292B410, 0x02928F00 }, /**< Chan = 086, TX = 910.591538, RX = 910.391400, DIFF = 0.200137 */
  { 0x0292C690, 0x0292A180 }, /**< Chan = 087, TX = 910.691438, RX = 910.491300, DIFF = 0.200137 */
  { 0x0292D910, 0x0292B400 }, /**< Chan = 088, TX = 910.791338, RX = 910.591200, DIFF = 0.200137 */
  { 0x0292EB90, 0x0292C680 }, /**< Chan = 089, TX = 910.891238, RX = 910.691100, DIFF = 0.200138 */
  { 0x0292FE10, 0x0292D900 }, /**< Chan = 090, TX = 910.991138, RX = 910.791000, DIFF = 0.200137 */
  { 0x02931090, 0x0292EB80 }, /**< Chan = 091, TX = 911.091038, RX = 910.890900, DIFF = 0.200137 */
  { 0x02932310, 0x0292FE00 }, /**< Chan = 092, TX = 911.190938, RX = 910.990800, DIFF = 0.200137 */
  { 0x02933590, 0x02931080 }, /**< Chan = 093, TX = 911.290838, RX = 911.090700, DIFF = 0.200137 */
  { 0x02934810, 0x02932300 }, /**< Chan = 094, TX = 911.390738, RX = 911.190600, DIFF = 0.200137 */
  { 0x02935A90, 0x02933580 }, /**< Chan = 095, TX = 911.490638, RX = 911.290500, DIFF = 0.200137 */
  { 0x02936D10, 0x02934800 }, /**< Chan = 096, TX = 911.590538, RX = 911.390400, DIFF = 0.200138 */
  { 0x02937F90, 0x02935A80 }, /**< Chan = 097, TX = 911.690438, RX = 911.490300, DIFF = 0.200137 */
  { 0x02939210, 0x02936D00 }, /**< Chan = 098, TX = 911.790338, RX = 911.590200, DIFF = 0.200137 */
  { 0x0293A490, 0x02937F80 }, /**< Chan = 099, TX = 911.890238, RX = 911.690100, DIFF = 0.200137 */
  { 0x0293B710, 0x02939200 }, /**< Chan = 100, TX = 911.990138, RX = 911.790000, DIFF = 0.200137 */
  { 0x0293C990, 0x0293A480 }, /**< Chan = 101, TX = 912.090037, RX = 911.889900, DIFF = 0.200137 */
  { 0x0293DC10, 0x0293B700 }, /**< Chan = 102, TX = 912.189938, RX = 911.989800, DIFF = 0.200137 */
  { 0x0293EE90, 0x0293C980 }, /**< Chan = 103, TX = 912.289838, RX = 912.089700, DIFF = 0.200138 */
  { 0x02940110, 0x0293DC00 }, /**< Chan = 104, TX = 912.389738, RX = 912.189600, DIFF = 0.200137 */
  { 0x02941390, 0x0293EE80 }, /**< Chan = 105, TX = 912.489638, RX = 912.289500, DIFF = 0.200137 */
  { 0x02942610, 0x02940100 }, /**< Chan = 106, TX = 912.589538, RX = 912.389400, DIFF = 0.200137 */
  { 0x02943890, 0x02941380 }, /**< Chan = 107, TX = 912.689438, RX = 912.489300, DIFF = 0.200137 */
  { 0x02944B10, 0x02942600 }, /**< Chan = 108, TX = 912.789338, RX = 912.589200, DIFF = 0.200138 */
  { 0x02945D90, 0x02943880 }, /**< Chan = 109, TX = 912.889238, RX = 912.689100, DIFF = 0.200137 */
  { 0x02947010, 0x02944B00 }, /**< Chan = 110, TX = 912.989138, RX = 912.789000, DIFF = 0.200137 */
  { 0x02948290, 0x02945D80 }, /**< Chan = 111, TX = 913.089038, RX = 912.888900, DIFF = 0.200137 */
  { 0x02949510, 0x02947000 }, /**< Chan = 112, TX = 913.188938, RX = 912.988800, DIFF = 0.200137 */
  { 0x0294A790, 0x02948280 }, /**< Chan = 113, TX = 913.288837, RX = 913.088700, DIFF = 0.200137 */
  { 0x0294BA10, 0x02949500 }, /**< Chan = 114, TX = 913.388738, RX = 913.188600, DIFF = 0.200137 */
  { 0x0294CC90, 0x0294A780 }, /**< Chan = 115, TX = 913.488638, RX = 913.288500, DIFF = 0.200138 */
  { 0x0294DF10, 0x0294BA00 }, /**< Chan = 116, TX = 913.588538, RX = 913.388400, DIFF = 0.200137 */
  { 0x0294F190, 0x0294CC80 }, /**< Chan = 117, TX = 913.688438, RX = 913.488300, DIFF = 0.200137 */
  { 0x02950410, 0x0294DF00 }, /**< Chan = 118, TX = 913.788338, RX = 913.588200, DIFF = 0.200137 */
  { 0x02951690, 0x0294F180 }, /**< Chan = 119, TX = 913.888238, RX = 913.688100, DIFF = 0.200137 */
  { 0x02952910, 0x02950400 }, /**< Chan = 120, TX = 913.988137, RX = 913.788000, DIFF = 0.200137 */
  { 0x02953B90, 0x02951680 }, /**< Chan = 121, TX = 914.088038, RX = 913.887900, DIFF = 0.200137 */
  { 0x02954E10, 0x02952900 }, /**< Chan = 122, TX = 914.187938, RX = 913.987800, DIFF = 0.200138 */
  { 0x02956090, 0x02953B80 }, /**< Chan = 123, TX = 914.287838, RX = 914.087700, DIFF = 0.200137 */
  { 0x02957310, 0x02954E00 }, /**< Chan = 124, TX = 914.387738, RX = 914.187600, DIFF = 0.200137 */
  { 0x02958590, 0x02956080 }, /**< Chan = 125, TX = 914.487638, RX = 914.287500, DIFF = 0.200137 */
  { 0x02959810, 0x02957300 }, /**< Chan = 126, TX = 914.587538, RX = 914.387400, DIFF = 0.200137 */
  { 0x0295AA90, 0x02958580 }, /**< Chan = 127, TX = 914.687438, RX = 914.487300, DIFF = 0.200138 */
};