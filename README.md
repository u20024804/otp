Erlang/OTP
==========

**Erlang** is a programming language used to build massively scalable soft
real-time systems with requirements on high availability. Some of its
uses are in telecom, banking, e-commerce, computer telephony and
instant messaging. Erlang's runtime system has built-in support for
concurrency, distribution and fault tolerance.

**OTP** is set of Erlang libraries and design principles providing
middle-ware to develop these systems. It includes its own distributed
database, applications to interface towards other languages, debugging
and release handling tools.

More information can be found at [erlang.org] [1].

Why forked?
-----------
Erlang/OTP was forked in order to work on implementing an LLVM
back-end for HiPE. The current work is focused on AMD64 architecture
but the back-end is meant to be target-independent (for the
architecture that the Erlang Run-Time System supports). Please take
some time and install [custom LLVM] [5] before moving forward because
it is an integral part of the back-end.

More information about the design decisions and the actual patch to be announced.

Building and Installing
-----------------------
*  Getting latest source code from [Github] [4]:

        git clone git://github.com/yiannist/otp.git otp

*  Compiling:

	    cd otp/
	    ./otp_build autoconf
	    ./configure
	    make

*  Installing (*optional*):

        sudo make install

*  Verifying that the installation was successful (this
   step considers [custom LLVM] [5] to be **already** successfully
   installed in your system): 

    1.  Write an Erlang module:
         
            -module(test).
            -export(hello/1).
            
            hello(Name) ->
                io:format("Hello ~w!~n", [Name]).

    2.  Fire the Erlang shell:

            yiannis@mosby [~/git/otp]>>= erl
            Erlang R14B04 (erts-5.8.5) [source] [64-bit] [smp:2:2] [rq:16]
            [async-threads:0] [hipe] [kernel-poll:false]

            Eshell V5.8.5  (abort with ^G)
            1>

    3.  Compile module to BEAM bytecode:

            1> c(foo).
            {ok,foo}

    4.  Compile whole module using the LLVM back-end:

            2> hipe:c(foo, [to_llvm]).
            {ok,foo}

    5.  It works! :-)

            3> foo:hello(world).	
            Hello world!	
            ok	 
            4>

Copyright and License
---------------------

> %CopyrightBegin%
>
> Copyright Ericsson AB 2010-2012. All Rights Reserved.
>
> The contents of this file are subject to the Erlang Public License,
> Version 1.1, (the "License"); you may not use this file except in
> compliance with the License. You should have received a copy of the
> Erlang Public License along with this software. If not, it can be
> retrieved online at http://www.erlang.org/.
>
> Software distributed under the License is distributed on an "AS IS"
> basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
> the License for the specific language governing rights and limitations
> under the License.
>
> %CopyrightEnd%



   [1]: http://www.erlang.org
   [2]: http://wiki.github.com/erlang/otp/submitting-patches
   [3]: http://www.erlang.org/faq.html
   [4]: http://github.com/yiannist/otp
   [5]: http://github.com/yiannist/llvm
