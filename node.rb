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

# Class Msg is used to modify/make messages sent between nodes
class Msg
  LENGTH = 20
  CONFIG = {
    # configuration defines four attributes to create, update and destroy nodes. Also added 
    # fragmentation implementation
    "type" => 0,
    "code" => 1,
    "ttl" => 4,
    "seq" => 5,
    "fragment_num" => 6,
    "fragment_seq" => 7,
    "checksum" => 19,
  }

  # For initializing the message
  def initialize(msg = nil)
    if msg.nil?
      @header = ((0).chr) * LENGTH
      @message = ""
    else
      @msg = msg
      @header = msg[0..(LENGTH - 1)]
      @message = msg[LENGTH..(msg.length - 1)]
    end
  end

 # Now implements checksum because of fragmentation
  def toString()
    @header[LENGTH - 1] = checksum()
    return @header + @message
  end

  def setHeader(header)
    @header = header
  end

  def getHeader()
    return @header
  end

  # Sets the configuration field to the n
  def setConfig(field_name, n)
    field = CONFIG[field_name]
    @header[field] = n.chr
  end

  # Sets the specified configuration field
  def getConfig(field_name)
    field = CONFIG[field_name]
    res = @header[field].ord
    return res
  end

  # Previously known as setIpAndHost - not accurate so we changed it to setMessage
  def setMessage(msg)
    @message = msg
  end

  # Get the message contents
  def getMessage()
    return @message
  end

  def splitStrBySize(str, size)
    return str.chars.each_slice(size).map(&:join)
  end

  # Fragmentation implementation
  def fragment()
    message = @message
    messageSize = message.bytesize()
    packets = []
    if messageSize < $mtu
      packets = [self]
    else
      message_split = splitStrBySize(message, $mtu)
      fragment_num = message_split.length
      fragment_seq = 1
      message_split.each do |msg|
        msg = Msg.new
        msg.setHeader(String.new(@header))
        msg.setConfig("fragment_num", fragment_num)
        msg.setConfig("fragment_seq", fragment_seq)
        msg.setMessage(msg)
        packets << msg
        fragment_seq += 1
      end
    end
    return packets
  end

  # Assembles the messages of all the fragments into one large message
  def assembleFragments(packets)
    message = ""
    header = String.new(packets[0].getHeader())
    msg = Msg.new
    msg.setHeader(header)
    msg.setConfig("fragment_num", 0)
    msg.setConfig("fragment_seq", 0)
    packets.each do |packet|
      message += packet.getMessage()
    end
    msg.setMessage(message)
    return msg
  end

  # Checksum implementation
  def checksum()
    check = @header[0].ord
    for i in (1..LENGTH - 2)
      check = check * (@header[i].ord)
    end
    return check.chr
  end

  # Validates the packets did not get corrupted/missing
  def validate()
    cs = checksum()
    return cs == @header[LENGTH - 1]
  end

end

# This method fill in nodes in between two src and des nodes.
def fillInNodes()
  msg = Msg.new
  msg.setConfig("type", 1)
  msg.setConfig("ttl", $ports.length)
  msg.setConfig("seq", nextSeqNum())
  msg_str = $hostname + "\t"
  if $neighbors.length > 0
    $neighbors.each do |dst, distance|
      msg_str += dst + "," + distance.to_s + "\t"
    end
    msg.setMessage(msg_str)
    $clients.each do |dst, client|  
      sendMessage(client, msg)
    end
  end
end

# This method return the next sequence number
def nextSeqNum()
  $sequence_num = ($sequence_num + 1) % 256
  return $sequence_num
end

# This method will be passed a message and client. It will get the type from that
# message and will run a specified method depending on that.
def runOperation(msg, client)
  case msg.getConfig("type")
  when 0; edgebReflex(msg.getMessage(), client)
  when 1; fillBack(msg)
  when 2; edgeuUpdate(msg.getMessage())
  when 3; pingCallBack(msg)
  when 4; tracerouteCallBack(msg)
  when 5; sendMsgCallBack(msg, client)
  else STDERR.puts "ERROR: INVALID MESSAGE \"#{msg}\""
  end
end

# This method compare both distance in two nodes 
def isSmaller(a, b)
  if b == "INF"
    return true
  elsif a == "INF"
    return false
  else
    return a < b
  end
end

# This method find the smallest node that closer to the set       
def findMin(temp_set)
  min_n = nil
  min_d = "INF"
  $dist.each do |node, dist|
    if isSmaller(dist, min_d) and !(temp_set.include? node)
      min_d = dist
      min_n = node
    end
  end
  return min_n
end

# This method run Dijkstra’s shortest path algorithm to update the routing table
def runDijkstra()   
  $dist.each do |node, dist|
    if node != $hostname
      $dist[node] = "INF"
    end
  end
  temp_set = []
  while temp_set.length < $networks.length
    curr = findMin(temp_set)
    temp_set << curr
    dist_curr = $dist[curr]
    n_tbl = $networks[curr]["neighbors"]
    n_tbl.each do |neighbor, dist|
      p_dist = dist_curr + dist
      if isSmaller(p_dist, $dist[neighbor])
        $dist[neighbor] = p_dist
        if curr != $hostname
          $next[neighbor] = $next[curr]
        end
      end
    end
  end
end

# This method check node whether two sets that they can reach same nodes
def checkNode()
  source_set = []
  neighbor_set = []
  $networks.each do |s, nb|
    source_set << s
    nb["neighbors"].each do |s_, dist|
      neighbor_set << s_
    end
  end
  source_set.sort!
  source_set.uniq!
  neighbor_set.sort!
  neighbor_set.uniq!
  return source_set == neighbor_set
end

# This method create a list of symmetric nodes correspond to the fillInNode() method
def fillBack(msg)
  ttl = msg.getConfig("ttl")
  sn = msg.getConfig("seq")
  if ttl == 0
    return
  else
    message = msg.getMessage()
    message_array = message.split("\t")
    host = message_array[0]
    if (host != $hostname and ($networks[host] == nil or $networks[host]["sn"] != sn))
      host_dist_tbl = Hash.new()
      for i in 1..(message_array.length - 1)
        neighbor_dist_pair = message_array[i].split(",")
        host_dist_tbl[neighbor_dist_pair[0]] = neighbor_dist_pair[1].to_i
      end
      $networks[host] = {"sn" => sn, "neighbors" => host_dist_tbl}
      msg.setConfig("ttl", ttl - 1)
      $clients.each do |dst, client|
        sendMessage(client, msg)
      end
      if checkNode()
        runDijkstra()
      end
    end
  end
end

# Send message will send the message over to the client. Will return false if 
# the bytes send is too large than the bytesize of the message
def sendMessage(client, msg)
  packets = msg.fragment()
  packets.each do |packet|
    to_send = packet.toString() + "\n"
    num_bytes = to_send.bytesize()
    check = client.write(to_send)
    if check < num_bytes
      return false
    end
  end
  return true
end

# This method will recieve the message and pass it to runOperation. Now implements fragmentation
def receiveMessage(client)
  while msg_str = client.gets
    # Ensures the message is valid
    if (msg_str.length >= Msg::LENGTH + 1 and Msg.new(msg_str.chop).validate)
      $mutex.synchronize {
        msg = Msg.new(msg_str.chop)
        fragment_seq = msg.getConfig("fragment_seq")
        fragment_num = msg.getConfig("fragment_num")

        # Checks to see if the message was fragmented
        if fragment_seq == 0
          runOperation(msg, client)
        else
          $receiver_buffer << msg
          if fragment_num == fragment_seq
            assembled_msg = assembleFragments($receiver_buffer)
            $receiver_buffer.clear()
            runOperation(assembled_msg, client)
          end
        end
      }   
    end
    # We need this sleep because Ruby will have a difficult time with memory management
    sleep(0.01)
  end
end

# This method runs edgeb on the node that was passed the message to run edgeb
def edgebReflex(msg, client)
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
  fillInNodes()
end

# This method update the node information
def edgeuUpdate(msg)
  msg = msg.split(' ')
  dst = msg[0]
  cost = msg[1].to_i
  $dist[dst] = cost
  $neighbors[dst] = cost
end

# This method is called when ping traverses through the network
def pingCallBack(msg)
  code = msg.getConfig("code")
  message_arr = msg.getMessage.split(' ')
  src = message_arr[0]
  dst = message_arr[1]
  seq_id = message_arr[2]

  # code will equal 0 when the method ping is called. It will rewrite the hostid. If it 
  # reached the correct destination, it will set the code to 1 then resend it back. Otherwise
  # it will forward it to the next client
  if code == 0
    if dst == $hostname
      msg.setConfig("code", 1)
      client = $clients[$next[src]]
      sendMessage(client, msg)
    else
      client = $clients[$next[dst]]
      sendMessage(client, msg)
    end
  
  # If code is not 0, and the src reached the correct host, it will print out the right
  # information. Note: once the src found the correct host, it wil delete itself from the 
  # ping_table. Otherwise, it will forward it to the next client.   
  else
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

# This method is called when traceroute traverses through the network
def tracerouteCallBack(msg)
  code = msg.getConfig("code")
  message_arr = msg.getMessage.split(' ')
  src = message_arr[0]
  dst = message_arr[1]
  host_id = message_arr[2]
  hop_count = message_arr[3]
  time = message_arr[4]

  # code will equal 0 when the method traceroute is called. It will rewrite the hostid, hop count
  # and the time and will send the message back
  if code == 0
    hop_count = (hop_count.to_i + 1).to_s
    return_msg = Array.new(message_arr)
    return_msg[2] = $hostname
    return_msg[3] = hop_count
    return_msg[4] = ($currtime.to_f.round(4) - time.to_f).round(4).abs.to_s
    send_back = Msg.new
    send_back.setConfig("type", 4)
    send_back.setConfig("code", 1)
    send_back.setMessage(return_msg.join(" "))
    sendMessage($clients[$next[src]], send_back)
    if dst != $hostname
      message_arr[3] = hop_count
      msg.setMessage(message_arr.join(" "))
      sendMessage($clients[$next[dst]], msg)
    end

  # If it isn't code 0, it try to find the src then print out the contents  
  else
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

# This method is called when sendmsg traverses through the network
def sendMsgCallBack(msg, client)
  message_arr = msg.getMessage().split(" ")
  
  # Removes and stores the src and dst from the message
  src = message_arr.shift()
  dst = message_arr.shift()
  to_print = "SNDMSG: %s --> %s"

  # If the destination reached the right host, it will print out the correct message
  # If not, it will forward it to the next client
  if dst == $hostname
    message_arr = message_arr.join(" ")
    STDOUT.puts(to_print % [src, message_arr])
  else
    k = $next[dst]
    forward_client = $clients[k]
    sendMessage(forward_client, msg)
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
  msg.setMessage(srcip + "," + dstip + "," + $hostname)
  sendMessage(s, msg)
  fillInNodes()
  Thread.new {
    receiveMessage(s)
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
    client.close
  end
  STDOUT.flush
  STDERR.flush
  exit(0)
end

# --------------------- Part 1 --------------------- # 
# This method delete the correspond node in $ips, $dist, 
# $ neighbors, $client and $next table.  
def edged(cmd)
  $ips.delete(cmd[0])
  $dist[cmd[0]] = "INF"
  $neighbors.delete(cmd[0])
  $next[cmd[0]] = "NA"
  client = $clients[cmd[0]]
  client.close()
  $clients.delete(cmd[0])
end

# This method reset the correspond distance, neighbors to new one
# it also send message to clients to update information in between 
def edgeu(cmd)
  $dist[cmd[0]] = cmd[1].to_i
  $neighbors[cmd[0]] = cmd[1].to_i
  client = $clients[cmd[0]]
  msg = Msg.new
  msg.setConfig("type", 2)
  msg.setMessage($hostname + " " + cmd[1].to_i.to_s)
  sendMessage(client, msg)
  fillInNodes()
end

# This method return the current status information 
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
# sendmsg will take the the message given in the command line and will send forward it 
# through the network until it reaches the correct destination node
def sendmsg(cmd)
	dst = cmd[0]
  msg = $hostname + " " + dst + " " + cmd[1..-1].join(" ")
  error_msg = "SNDMSG ERROR: HOST UNREACHABLE"

  # Make sure dst is reachable by checking it's next table, making sure it's not NA
  # and that the client table can find the right client
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
  packet.setConfig("type", 5)
  packet.setConfig("code", 0)
  packet.setMessage(msg)

  success = sendMessage(client, packet)
  if !success
    STDOUT.puts(error_msg)
  end
end

# ping will traverse through the network looking for the correct destination and will return
# sequence number, target node, and rtt
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

  # This will iterate through the number of pings given on the command line. It will setup the 
  # proper message for pingCallBack and adds the current time to the ping table with the key
  # of the sequence number. It will then check if ping_table has that key still (should be removed
  # by pingCallBack) so if it still exists, then the host was not reached.
  for seq_id in (0..(n - 1))
    msg = Msg.new
    msg.setConfig("type", 3)
    msg.setConfig("code", 0)
    msg.setMessage($hostname + " " + dst + " " + seq_id.to_s)
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

# traceroute will run through the network and find all the nodes in between the src and dst nodes
def traceroute(cmd)
	dst = cmd[0]

  # Check to see if there is a next hop
  next_hop = $next[dst]
  if next_hop == "NA"
    STDOUT.puts "TRACEROUTE ERROR: HOST UNREACHABLE"
    return
  end

  # This will print out itself with hop 0 and time 0.00
	STDOUT.puts("0 " + $hostname + " 0.00")
  
  if next_hop == $hostname
    return
  end

  # Sets up the message for tracerouteCallBack
  client = $clients[next_hop]
  msg = Msg.new
  msg.setConfig("type", 4)
  msg.setConfig("code", 0)
  msg.setMessage($hostname + " " + dst + " " + dst + " 0 " + $currtime.to_f.round(4).to_s)
  $traceroute_finish = false
  $hop_counter = "1"
  sendMessage(client, msg)

  start_time = $currtime
  while $currtime - start_time < $ping_timeout
    if $traceroute_finish
      return
    end
    sleep(0.1)
  end
	STDOUT.puts("TIMEOUT ON HOPCOUNT " + $hop_counter)
end

# --------------------- Part 3 --------------------- # 
# Starts the TCPServer
def startServer()
	server = TCPServer.open($ports[$hostname])
	loop {
		Thread.start(server.accept) do |client|
	    	receiveMessage(client)
		end
	}
end

# Will update the routing table using fillInNodes() every update interval specified
# by the configuration file
def updateTime()
	loop {
    $currtime += 0.01
    $flood_trigger += 0.01
    if $flood_trigger >= $update_interval
      $flood_trigger = 0
      Thread.new {
        $mutex.synchronize {
          fillInNodes()
        }
      }
    end
    sleep(0.01)
	}
end

# do main loop here.... 
def main()

	while(line = STDIN.gets())
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
	end

end

# Reads the node file and initializes all corresponding global variables
def readNodeFile(filename)
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

# Reads the configuration file and initializes all corresponding global variables
def readConfigFile(filename)
  f = File.open(filename, "r")
  f.each_line do |line|
    line = line.strip().split("=")
    option = line[0].upcase
    value = Integer(line[1])
    if option == "UPDATEINTERVAL"
      $update_interval = value
    elsif option == "MAXPAYLOAD"
      $mtu = value
    elsif option == "PINGTIMEOUT"
      $ping_timeout = value
    end
  end
  f.close()
end

def setup(hostname, port, nodes, config)
  $hostname = hostname
	$port = port
  readNodeFile(nodes)
	readConfigFile(config)
  $dist[hostname] = 0
	$next[hostname] = hostname
	$networks[$hostname] = {"neighbors" => $neighbors}
  $currtime = Time.now
  $flood_trigger = 0
	Thread.new {
   	updateTime()
  }
	Thread.new {
    	startServer()
  }
 	main()
end

setup(ARGV[0], ARGV[1], ARGV[2], ARGV[3])





