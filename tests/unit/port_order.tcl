yosys -import

set sv_file [file join [pwd] port_order.sv]
set first_dump [file join /tmp "yosys_slang_port_order_[pid]_a.il"]
set second_dump [file join /tmp "yosys_slang_port_order_[pid]_b.il"]

proc dump_port_order {sv_file dump_file} {
	design -reset
	read_slang --no-proc $sv_file
	hierarchy -top port_order
	write_rtlil $dump_file
}

proc normalized_rtlil {dump_file} {
	set fd [open $dump_file r]
	set text [read $fd]
	close $fd

	regsub -all {autoidx [0-9]+} $text {autoidx <N>} text
	regsub -all {\$[0-9]+} $text {$<N>} text
	return $text
}

dump_port_order $sv_file $first_dump
dump_port_order $sv_file $second_dump

set first_text [normalized_rtlil $first_dump]
set second_text [normalized_rtlil $second_dump]

file delete -force $first_dump $second_dump

foreach expected_port {
	{wire width 2 input 1 \sel}
	{wire width 8 input 2 \a}
	{wire width 8 input 3 \b}
	{wire width 8 input 4 \c}
	{wire width 8 output 5 \y}
} {
	if {[string first "\n  $expected_port\n" $first_text] < 0} {
		error "missing source-ordered RTLIL port: $expected_port"
	}
}

if {$first_text ne $second_text} {
	error "port_order RTLIL output changed between identical reads"
}
