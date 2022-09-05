#!/bin/bash
 ################################################################
 # $ID: rename-clean.sh 一, 29  8 2022 15:57:40 +0800  mhfan $ #
 #                                                              #
 # Maintainer:  范美辉 (MeiHui FAN) <mhfan@ustc.edu>            #
 #                                                              #
 # Copyright (c) 2022 M.H.Fan, All Rights Reserved.             #
 #                                                              #
 # Last modified: 一, 29  8 2022 15:58:36 +0800       by mhfan #
 ################################################################

# https://www.me.uk/cards/makeadeck.cgi
# https://github.com/revk/SVG-playing-cards

suits=(S H C D);
court=(T J Q K);
for ((i=0; i < 4; i+=1)) do
    n=1; mv $(printf %03d $((n*2-1+i*13*2))).svg A${suits[i]}.svg
    for ((n=2;  n < 10; n+=1)) do
         mv $(printf %03d $((n*2-1+i*13*2))).svg ${n}${suits[i]}.svg
    done
    for ((n=10; n < 14; n+=1)) do
         mv $(printf %03d $((n*2-1+i*13*2))).svg ${court[$((n-10))]}${suits[i]}.svg
    done
done

mv 105.svg JokerR.svg
mv 107.svg JokerB.svg
mv 108.svg back-maze.svg
for ((n=2; n < 108; n+=2)) do rm -f $(printf %03d n).svg; done

 # vim:sts=4 ts=8 sw=4 noet
