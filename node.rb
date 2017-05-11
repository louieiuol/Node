require 'set'
require 'socket'
require 'thread'

#Global Variables
$port = nil
$hostname = nil
$mutex = Mutex.new
$clients = Hash.new()
$dist = Hash.new("INF")
$next = Hash.new("NA")
$neighbors = Hash.new()
$ips = Hash.new()
$ports = Hash.new()
$server = nil
$ping_timeout = nil
$mtu = nil
$update_interval = nil
$sequence_num = 0
$networks = Hash.new()
$ping_table = Hash.new()
$currtime = nil
$receiver_buffer = []
$flood_trigger = 0
$traceroute_finish = true
$hop_counter = "1"

# SENDMSG Constants and fields
$SENDMSG_HEADER_TYPE = 20

class Msg
  HEADER_LENGTH = 20 # header length in bytes
  HEADER_CONFIG = {
    "type" => [0,0], # type field = [start_index, end_index]
    "code" => [1,1],
    "checksum" => [19,19],
    "ttl" => [4,4],
    "seq" => [5,5],
    "fragment_num" => [6,6],
    "fragment_seq" => [7,7]
  }

  def initialize(msg = nil)
    if msg.nil?
      @header = ((0).chr) * HEADER_LENGTH
      @payload = ""
    else
      @msg = msg
      @header = msg[0..(HEADER_LENGTH - 1)]
      @payload = msg[HEADER_LENGTH..(msg.length - 1)]
    end
  end

  def toString()
    @header[HEADER_LENGTH - 1] = checksum()
    return @header + @payload
  end

  def setHeader(header)
    @header = header
  end

  def getHeader()
    return @header
  end

  def setConfig(field_name, n)
    field_range = HEADER_CONFIG[field_name]
    # STDOUT.puts n
    @header[field_range[0]..field_range[1]] = n.chr
  end

  def getHeaderField(field_name)
    field_range = HEADER_CONFIG[field_name]
    res = @header[field_range[0]..field_range[1]].ord
    return res
  end

  def setIpAndHost(payload)
    @payload = payload
  end

  def getPayLoad()
    return @payload
  end

  def fragment()
    payload_str = @payload
    payload_size = payload_str.bytesize()
    packet_list = []
    if payload_size < $mtu
      packet_list = [self]
    else
      num_of_fragments = (payload_size / $mtu).ceil
      
      payload_list = Util.split_str_by_size(payload_str, $mtu)
      
      fragment_num = payload_list.length
      fragment_seq = 1

      payload_list.each do |payload|
        msg = Msg.new
        msg.setHeader(String.new(@header))
        msg.setConfig("fragment_num", fragment_num)
        msg.setConfig("fragment_seq", fragment_seq)
        msg.setIpAndHost(payload)
        packet_list << msg
        fragment_seq += 1
      end
    end

    return packet_list
  end

  def checksum()
    res = @header[0].ord
    for i in (1..HEADER_LENGTH - 2)
      res = res ^ (@header[i].ord)
    end
    return res.chr
  end

  def validate()
    cs = checksum()
    return cs == @header[HEADER_LENGTH - 1]
  end
end

def sendMessage(client, msg)
  packet_list = msg.fragment()
  packet_list.each do |packet|
    to_send = packet.toString() + "\n"
    num_bytes = to_send.bytesize()
    check = client.write(to_send)
    if check < num_bytes
      return false
    end
  end
  return true
end

module CtrlMsg

  def CtrlMsg.callback(msg, client)
    case msg.getHeaderField("type")
    when 0; CtrlMsg.edgeb(msg.getPayLoad(), client)
    when 1; CtrlMsg.floodCallBack(msg)
    when 2; CtrlMsg.edgeu(msg.getPayLoad())
    when 3; CtrlMsg.pingCallBack(msg)
    when 4; CtrlMsg.tracerouteCallBack(msg)
    when $SENDMSG_HEADER_TYPE; CtrlMsg.sendmsgCallBack(msg, client)
    else STDERR.puts "ERROR: INVALID MESSAGE \"#{msg}\""
    end
  end

  def CtrlMsg.receive(client)
    while msg_str = client.gets
      if (msg_str.length >= Msg::HEADER_LENGTH + 1 and Msg.new(msg_str.chop).validate)
        $mutex.synchronize {
          msg = Msg.new(msg_str.chop)
#           STDOUT.puts "In receive"
#           STDOUT.puts msg_str.length
#           STDOUT.puts msg.getPayLoad
          fragment_seq = msg.getHeaderField("fragment_seq")
          fragment_num = msg.getHeaderField("fragment_num")
          if fragment_seq == 0
            CtrlMsg.callback(msg, client)
          else
            $receiver_buffer << msg
            if fragment_num == fragment_seq
              res_msg = Util.assemble($receiver_buffer)
              $receiver_buffer.clear()
              CtrlMsg.callback(res_msg, client)
            end
          end
        }   
      end
      sleep(0.01)
    end
  end

  def CtrlMsg.edgeb(msg, client)
    msg = msg.split(',')
    dstip = msg[0]
    srcip = msg[1]
    dst = msg[2]
    $ips[$hostname] = srcip
    $ips[dst] = dstip
    $dist[dst] = 1
    $neighbors[dst] = 1
    $next[dst] = dst
    $clients[dst] = client
    CtrlMsg.flood()
    STDOUT.puts "CTRLMSG-EDGEB: SUCCESS"
  end

  def CtrlMsg.edgeu(msg)
    msg = msg.split(' ')
    dst = msg[0]
    cost = msg[1].to_i
    $dist[dst] = cost
    $neighbors[dst] = cost
    CtrlMsg.flood()
    STDOUT.puts "CTRLMSG-EDGEU: SUCCESS"
  end

  def CtrlMsg.flood()
    msg = Msg.new
    msg.setConfig("type", 1)
    msg.setConfig("ttl", $ports.length)
    msg.setConfig("seq", Util.nextSeqNum())
    msg_str = $hostname + "\t"
    if $neighbors.length > 0
      $neighbors.each do |dst, distance|
        msg_str += dst + "," + distance.to_s + "\t"
      end
      msg.setIpAndHost(msg_str)
      $clients.each do |dst, client|  
        sendMessage(client, msg)
      end
#       STDOUT.puts "CTRLMSG-FLOOD: SUCCESS"
    end
  end

  def CtrlMsg.floodCallBack(msg)
#     STDOUT.puts "In flood call back"
#     STDOUT.puts msg.getPayLoad()
    ttl = msg.getHeaderField("ttl")
    sn = msg.getHeaderField("seq")
    if ttl == 0
      return
    else
      msg_payload = msg.getPayLoad()
      payload_array = msg_payload.split("\t")
      host = payload_array[0]
      if (host != $hostname and ($networks[host] == nil or $networks[host]["sn"] != sn))
        host_dist_tbl = Hash.new()
        for i in 1..(payload_array.length - 1)
          neighbor_dist_pair = payload_array[i].split(",")
          host_dist_tbl[neighbor_dist_pair[0]] = neighbor_dist_pair[1].to_i
        end
        $networks[host] = {"sn" => sn, "neighbors" => host_dist_tbl}
        msg.setConfig("ttl", ttl - 1)
        $clients.each do |dst, client|
          sendMessage(client, msg)
        end
        if Util.checkTopology
          Util.updateRoutingTable()
        end
#         STDOUT.puts "CTRLMSG-FLOODCALLBACK: SUCCESS"
      end
    end
    
  end

  def CtrlMsg.pingCallBack(msg)
    code = msg.getHeaderField("code")
    payload = msg.getPayLoad.split(' ')
    src = payload[0]
    dst = payload[1]
    seq_id = payload[2]
    if code == 0
      # forwrd
      if dst == $hostname
        msg.setConfig("code", 1)
        client = $clients[$next[src]]
        sendMessage(client, msg)
      else
        client = $clients[$next[dst]]
        sendMessage(client, msg)
      end
    else
      # backward
      if src == $hostname
        if $ping_table.has_key?(seq_id)
          rtp = $currtime - $ping_table[seq_id]
          STDOUT.puts (seq_id + " " + dst + " " + rtp.to_s)
          $ping_table.delete(seq_id)
        end
      else
        client = $clients[$next[src]]
        sendMessage(client, msg)
      end
    end
  end

  def CtrlMsg.tracerouteCallBack(msg)
    code = msg.getHeaderField("code")
    payload = msg.getPayLoad.split(' ')
    src = payload[0]
    dst = payload[1]
    host_id = payload[2]
    hop_count = payload[3]
    time = payload[4]
    if code == 0
      # forwrd
      hop_count = (hop_count.to_i + 1).to_s
      ret_payload = Array.new(payload)
      ret_payload[2] = $hostname
      ret_payload[3] = hop_count
      ret_payload[4] = ($currtime.to_f.round(4) - time.to_f).round(4).abs.to_s
      ret_msg = Msg.new
      ret_msg.setConfig("type", 4)
      ret_msg.setConfig("code", 1)
      ret_msg.setIpAndHost(ret_payload.join(" "))
      sendMessage($clients[$next[src]], ret_msg)
      if dst != $hostname
        payload[3] = hop_count
        msg.setIpAndHost(payload.join(" "))
        sendMessage($clients[$next[dst]], msg)
      end
    else
      # backward
      if src == $hostname
        STDOUT.puts(hop_count + " " + host_id + " " + time)
        $hop_counter = (hop_count.to_i + 1).to_s
        if host_id == dst 
          $traceroute_finish = true
        end
      else
        client = $clients[$next[src]]
        sendMessage(client, msg)
      end
    end
  end

  def CtrlMsg.sendmsgCallBack(msg, client)
    code = msg.getHeaderField("code")
    payload = msg.getPayLoad().split(" ")
    
    src = payload.shift()
    dst = payload.shift()
    
    to_print = "SNDMSG: %s --> %s"

    if dst == $hostname
      payload = payload.join(" ")
      STDOUT.puts(to_print % [src, payload])
    else
      k = $next[dst]
      forward_client = $clients[k]
      sendMessage(forward_client, msg)
    end
  end
  
end

module Util
  def Util.readNodeFile(filename)
    f = File.open(filename, "r")
    f.each_line do |line|
      line = line.strip()
      arr = line.split(',')
      node = arr[0]
      port = arr[1]
      $ports[node] = port
      $dist[node] = "INF"
      $next[node] = "NA"
    end
    f.close
  end

  def Util.parse_config_file(fname)
    f = File.open(fname, "r")
    update_interval = mtu = ping_timeout = nil
    f.each_line do |line|
      line = line.strip().split("=")
      option = line[0].upcase
      value = Integer(line[1])
      if option == "UPDATEINTERVAL"
        update_interval = value
      elsif option == "MAXPAYLOAD"
        mtu = value
      elsif option == "PINGTIMEOUT"
        ping_timeout = value
      end
    end
    f.close()

    return update_interval, mtu, ping_timeout
  end

  def Util.ipToByte(ip)
    ip_seg = ip.split('.')
    res = ""
    for i in 0..3
      res += ip_seg[i].to_i.chr
    end
    return res
  end

  def Util.byteToIp(byte)
    temp = []
    for i in 0..3
      temp[i] = byte[i].ord.to_s
    end
    return temp[0] + "." + temp[1] + "." + temp[2] + "." + temp[3]
  end

  def Util.nextSeqNum()
    $sequence_num = ($sequence_num + 1) % 256
    return $sequence_num
  end

  def Util.isSmaller(a, b)
    if b == "INF"
      return true
    elsif a == "INF"
      return false
    else
      return a < b
    end
  end
        
  def Util.findMinDistNode(sptSet)
    min_dist = "INF"
    min_node = nil
    $dist.each do |node, dist|
      if isSmaller(dist, min_dist) and !(sptSet.include? node)
        min_dist = dist
        min_node = node
      end
    end
    return min_node
  end

  def Util.updateRoutingTable()
  # Dijkstra’s shortest path algorithm    
    $dist.each do |node, dist|
      if node != $hostname
        $dist[node] = "INF"
      end
    end
    sptSet = []
    while sptSet.length < $networks.length
      current_node = findMinDistNode(sptSet)
      sptSet << current_node
      dist_to_current_node = $dist[current_node]
      neighbor_dist_tbl = $networks[current_node]["neighbors"]
      neighbor_dist_tbl.each do |neighbor, dist|
        proposed_dist = dist_to_current_node + dist
        if isSmaller(proposed_dist, $dist[neighbor])
          $dist[neighbor] = proposed_dist
          if current_node != $hostname
            $next[neighbor] = $next[current_node]
          end
        end
      end
    end
  end

  def Util.checkTopology()
    # check whether the network topology is complete
    src = []
    neighbors = []
    $networks.each do |s, nb|
      src << s
      nb["neighbors"].each do |s_, dist|
        neighbors << s_
      end
    end
    src = src.to_set
    neighbors = neighbors.to_set
    return src == neighbors
  end

  def Util.split_str_by_size(str, size)
    return str.chars.each_slice(size).map(&:join)
  end

  def Util.assemble(packet_list)
    # assert_operator packet_list.length, :>, 0
    payload_full_str = ""
    hdr = String.new(packet_list[0].getHeader())
    msg = Msg.new
    msg.setHeader(hdr)
    msg.setConfig("fragment_num", 0)
    msg.setConfig("fragment_seq", 0)
    packet_list.each do |packet|
      payload_full_str += packet.getPayLoad()
    end
    msg.setIpAndHost(payload_full_str)
    return msg
  end

end

# --------------------- Part 0 --------------------- # 
def edgeb(cmd)
  # cmd is a list of arguments given in the call cmd[0] -> source ip, cmd[1] -> dest ip, cmd[2] -> dest #
  srcip = cmd[0]
  dstip = cmd[1]
  dst = cmd[2]
  $neighbors[dst] = 1
  $next[dst] = dst
  $ips[$hostname] = srcip
  $ips[dst] = dstip
  $dist[dst] = 1
  port = $ports[dst]

   # Opens TCP socket
  s = TCPSocket.open(dstip, port)
  $clients[dst] = s

  # This will create a new message, setting it's type to 0 (edgebReflex) and pass in
  # the ip of the host, destination, and the hostname
  msg = Msg.new
  msg.setConfig("type", 0)
  msg.setIpAndHost(srcip + "," + dstip + "," + $hostname)
  sendMessage(s, msg)
  CtrlMsg.flood()
  Thread.new {
    CtrlMsg.receive(s)
  }
end

def dumptable(cmd)
  output = File.open(cmd[0], "w")
  tempArr = Array.new
  count = 0
  
  # This loop will run through all the ports in the port list "ports". It will
  # make sure that the hostname is not the destination, that there is a next hop 
  # and a distance. This will also keep a counter for how many entires in our routing table
  $ports.each do |dst, port|
    nextHop = $next[dst]
    distance = $dist[dst]
    if (($hostname != dst) && (nextHop != "NA") && (distance != "INF"))
      tempArr[count] = [$hostname, dst, nextHop, distance]
      count = count + 1
    end
  end

  # We then sort the routing table then pass it into output
  i = 0
  sorted = tempArr.sort {|a,b| a[1] <=> b[1]}
  while i < count
    resp = sorted[i]
    output << resp[0] << "," << resp[1] << "," << resp[2] << "," << resp[3] << "\n"
    i = i + 1
  end
  output.close
end

def shutdown(cmd)
    if $server != nil
      $server.close
    end
    $clients.each do |hostname, client|
      STDOUT.puts "Close connection to #{hostname}"
      client.close
    end
    STDOUT.puts "SHUTDOWN: SUCCESS"
    STDOUT.flush
    STDERR.flush
    exit(0)
end

# --------------------- Part 1 --------------------- # 
def edgeu(cmd)
	dst = cmd[0]
    cost = cmd[1].to_i
    $dist[dst] = cost
    $neighbors[dst] = cost
    client = $clients[dst]
    msg = Msg.new
    msg.setConfig("type", 2)
    msg.setIpAndHost($hostname + " " + cost.to_s)
    sendMessage(client, msg)
    CtrlMsg.flood()
    STDOUT.puts "EDGEU: SUCCESS"
end

def edged(cmd)
	dst = cmd[0]
    $ips.delete(dst)
    $dist[dst] = "INF"
    $neighbors.delete(dst)
    $next[dst] = "NA"
    client = $clients[dst]
    client.close()
    $clients.delete(dst)
    CtrlMsg.flood()
    STDOUT.puts "EDGED: SUCCESS"
end

def status()
	neighbors = []
    $neighbors.each do |node, distance|
      neighbors << node
    end
    neighbors.sort
    msg = "Name: " + $hostname + "\n"
    msg += "Port: " + $port + "\n"
    msg += "Neighbors: " 
    neighbors.each do |node|
      msg += node + ","
    end
    if msg[-1] == ","
      msg = msg.chop
    end
    STDOUT.puts msg
end

# --------------------- Part 2 --------------------- # 
def sendmsg(cmd)
	dst = cmd[0]
   
    msg = $hostname + " " + dst + " " + cmd[1..-1].join(" ")
  
    error_msg = "SENDMSG ERROR: HOST UNREACHABLE"

    # Make sure dst is reachable
    if ($next.include?(dst) && $next[dst] != "NA" &&
        $clients.has_key?($next[dst]))
      next_hop = $next[dst]
    else
      STDOUT.puts(error_msg)
      return
    end
    
    client = $clients[next_hop]
    
    # Construct the packet
    packet = Msg.new()
    packet.setConfig("type", $SENDMSG_HEADER_TYPE)
    packet.setConfig("code", 0)
    packet.setIpAndHost(msg)

    success = sendMessage(client, packet)
    if !success
      STDOUT.puts(error_msg)
    end
end

def ping(cmd)
	dst = cmd[0]
    next_hop = $next[dst]
    if next_hop == "NA" || next_hop == $hostname
		STDOUT.puts "PING ERROR: HOST UNREACHABLE"
      	return
    end
    n = cmd[1].to_i
    delay = cmd[2].to_i
    client = $clients[next_hop]
    for seq_id in (0..(n - 1))
      msg = Msg.new
      msg.setConfig("type", 3)
      msg.setConfig("code", 0)
      msg.setIpAndHost($hostname + " " + dst + " " + seq_id.to_s)
      $ping_table[seq_id.to_s] = $currtime
      sendMessage(client, msg)
      Thread.new {
        seq_id_ = seq_id
        sleep($ping_timeout)
        if $ping_table.has_key?(seq_id_.to_s)
			STDOUT.puts "PING ERROR: HOST UNREACHABLE"
        end
        $ping_table.delete(seq_id_.to_s)
      }
      sleep(delay)
    end
end

def traceroute(cmd)
	dst = cmd[0]
    next_hop = $next[dst]
    if next_hop == "NA"
		STDOUT.puts "TRACEROUTE ERROR: HOST UNREACHABLE"
      	return
    end
	STDOUT.puts("0 " + $hostname + " 0.00")
    if next_hop == $hostname
      return
    end
    client = $clients[next_hop]
    msg = Msg.new
    msg.setConfig("type", 4)
    msg.setConfig("code", 0)
    msg.setIpAndHost($hostname + " " + dst + " " + dst + " 0 " + $currtime.to_f.round(4).to_s)
    $traceroute_finish = false
    $hop_counter = "1"
    sendMessage(client, msg)
    start_time = $currtime
    while $currtime - start_time < $ping_timeout
      if $traceroute_finish
		STDOUT.puts "TRACEROUTE: SUCCESS"
        return
      end
      sleep(0.1)
    end
	STDOUT.puts("TIMEOUT ON HOPCOUNT " + $hop_counter)
end

# --------------------- Part 3 --------------------- # 

def startServer()
	server = TCPServer.open($ports[$hostname])
	loop {
		Thread.start(server.accept) do |client|
	    	CtrlMsg.receive(client)
		end
	}
end

def updateTime()
	loop {
			$currtime += 0.01
      $flood_trigger += 0.01
      if $flood_trigger >= $update_interval
        $flood_trigger = 0
        Thread.new {
          $mutex.synchronize {
            CtrlMsg.flood()
          }
        }
      end
			sleep(0.01)
	}
end

# do main loop here.... 
def main()

	while(line = STDIN.gets())
# 		$mutex.synchronize {
			line = line.strip()
			arr = line.split(' ')
			cmd = arr[0]
			args = arr[1..-1]
			case cmd
			when "EDGEB"; edgeb(args)
			when "EDGED"; edged(args)
			when "EDGEU"; edgeu(args)
			when "DUMPTABLE"; dumptable(args)
			when "SHUTDOWN"; shutdown(args)
			when "STATUS"; status()
			when "SNDMSG"; sendmsg(args)
			when "PING"; ping(args)
			when "TRACEROUTE"; traceroute(args)
			else STDERR.puts "ERROR: INVALID COMMAND \"#{cmd}\""
			end
# 		}
	end

end

def setup(hostname, port, nodes, config)
	$currtime = Time.now
  $flood_trigger = 0
	Thread.new {
   	updateTime()
  }
	$hostname = hostname
	$port = port
	Util.readNodeFile(nodes)
	$update_interval, $mtu, $ping_timeout = Util.parse_config_file(config)
	$dist[hostname] = 0
	$next[hostname] = hostname
	$networks[$hostname] = {"neighbors" => $neighbors}
	Thread.new {
    	startServer()
  	}

 	main()
end

setup(ARGV[0], ARGV[1], ARGV[2], ARGV[3])





