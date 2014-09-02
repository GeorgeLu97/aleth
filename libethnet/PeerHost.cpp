/*
	This file is part of cpp-ethereum.

	cpp-ethereum is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	cpp-ethereum is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with cpp-ethereum.  If not, see <http://www.gnu.org/licenses/>.
*/
/** @file PeerHost.cpp
 * @authors:
 *   Gav Wood <i@gavwood.com>
 *   Eric Lombrozo <elombrozo@gmail.com>
 * @date 2014
 */

#include "PeerHost.h"

#include <sys/types.h>
#ifdef _WIN32
// winsock is already included
// #include <winsock.h>
#else
#include <ifaddrs.h>
#endif

#include <set>
#include <chrono>
#include <thread>
#include <libethential/Common.h>
#include <libethcore/UPnP.h>
#include <libethcore/Exceptions.h>
#include "PeerSession.h"
using namespace std;
using namespace eth;

// Addresses we will skip during network interface discovery
// Use a vector as the list is small
// Why this and not names?
// Under MacOSX loopback (127.0.0.1) can be named lo0 and br0 are bridges (0.0.0.0)
static const set<bi::address> c_rejectAddresses = {
	{bi::address_v4::from_string("127.0.0.1")},
	{bi::address_v6::from_string("::1")},
	{bi::address_v4::from_string("0.0.0.0")},
	{bi::address_v6::from_string("::")}
};

PeerHost::PeerHost(std::string const& _clientVersion, unsigned short _port, string const& _publicAddress, bool _upnp, bool _localNetworking):
	m_clientVersion(_clientVersion),
	m_listenPort(_port),
	m_localNetworking(_localNetworking),
	m_acceptor(m_ioService, bi::tcp::endpoint(bi::tcp::v4(), _port)),
	m_socket(m_ioService),
	m_key(KeyPair::create())
{
	populateAddresses();
	determinePublic(_publicAddress, _upnp);
	ensureAccepting();
	m_lastPeersRequest = chrono::steady_clock::time_point::min();
	clog(NetNote) << "Id:" << m_key.address().abridged();
}

PeerHost::PeerHost(std::string const& _clientVersion, string const& _publicAddress, bool _upnp, bool _localNetworking):
	m_clientVersion(_clientVersion),
	m_listenPort(0),
	m_localNetworking(_localNetworking),
	m_acceptor(m_ioService, bi::tcp::endpoint(bi::tcp::v4(), 0)),
	m_socket(m_ioService),
	m_key(KeyPair::create())
{
	m_listenPort = m_acceptor.local_endpoint().port();

	// populate addresses.
	populateAddresses();
	determinePublic(_publicAddress, _upnp);
	ensureAccepting();
	m_lastPeersRequest = chrono::steady_clock::time_point::min();
	clog(NetNote) << "Id:" << m_key.address().abridged();
}

PeerHost::PeerHost(std::string const& _clientVersion):
	m_clientVersion(_clientVersion),
	m_listenPort(0),
	m_acceptor(m_ioService, bi::tcp::endpoint(bi::tcp::v4(), 0)),
	m_socket(m_ioService),
	m_key(KeyPair::create())
{
	// populate addresses.
	populateAddresses();
	m_lastPeersRequest = chrono::steady_clock::time_point::min();
	clog(NetNote) << "Id:" << m_key.address().abridged();
}

PeerHost::~PeerHost()
{
	disconnectPeers();
}

unsigned PeerHost::protocolVersion() const
{
	return 0;
}

void PeerHost::registerPeer(std::shared_ptr<PeerSession> _s, vector<string> const& _caps)
{
	{
		Guard l(x_peers);
		m_peers[_s->m_id] = _s;
	}
	for (auto const& i: _caps)
		if (haveCapability(i))
			_s->m_capabilities[i] = shared_ptr<PeerCapability>(m_capabilities[i]->newPeerCapability(_s.get()));
}

void PeerHost::disconnectPeers()
{
	for (unsigned n = 0;; n = 0)
	{
		{
			Guard l(x_peers);
			for (auto i: m_peers)
				if (auto p = i.second.lock())
				{
					p->disconnect(ClientQuit);
					n++;
				}
		}
		if (!n)
			break;
		m_ioService.poll();
		this_thread::sleep_for(chrono::milliseconds(100));
	}

	delete m_upnp;
}

void PeerHost::seal(bytes& _b)
{
	_b[0] = 0x22;
	_b[1] = 0x40;
	_b[2] = 0x08;
	_b[3] = 0x91;
	uint32_t len = (uint32_t)_b.size() - 8;
	_b[4] = (len >> 24) & 0xff;
	_b[5] = (len >> 16) & 0xff;
	_b[6] = (len >> 8) & 0xff;
	_b[7] = len & 0xff;
}

void PeerHost::determinePublic(string const& _publicAddress, bool _upnp)
{
	if (_upnp)
		try
		{
			m_upnp = new UPnP;
		}
		catch (NoUPnPDevice) {}	// let m_upnp continue as null - we handle it properly.

	bi::tcp::resolver r(m_ioService);
	if (m_upnp && m_upnp->isValid() && m_peerAddresses.size())
	{
		clog(NetNote) << "External addr:" << m_upnp->externalIP();
		int p = m_upnp->addRedirect(m_peerAddresses[0].to_string().c_str(), m_listenPort);
		if (p)
			clog(NetNote) << "Punched through NAT and mapped local port" << m_listenPort << "onto external port" << p << ".";
		else
		{
			// couldn't map
			clog(NetWarn) << "Couldn't punch through NAT (or no NAT in place). Assuming" << m_listenPort << "is local & external port.";
			p = m_listenPort;
		}

		auto eip = m_upnp->externalIP();
		if (eip == string("0.0.0.0") && _publicAddress.empty())
			m_public = bi::tcp::endpoint(bi::address(), (unsigned short)p);
		else
		{
			m_public = bi::tcp::endpoint(bi::address::from_string(_publicAddress.empty() ? eip : _publicAddress), (unsigned short)p);
			m_addresses.push_back(m_public.address().to_v4());
		}
	}
	else
	{
		// No UPnP - fallback on given public address or, if empty, the assumed peer address.
		m_public = bi::tcp::endpoint(_publicAddress.size() ? bi::address::from_string(_publicAddress)
									: m_peerAddresses.size() ? m_peerAddresses[0]
									: bi::address(), m_listenPort);
		m_addresses.push_back(m_public.address().to_v4());
	}
}

void PeerHost::populateAddresses()
{
#ifdef _WIN32
	WSAData wsaData;
	if (WSAStartup(MAKEWORD(1, 1), &wsaData) != 0)
		throw NoNetworking();

	char ac[80];
	if (gethostname(ac, sizeof(ac)) == SOCKET_ERROR)
	{
		clog(NetWarn) << "Error " << WSAGetLastError() << " when getting local host name.";
		WSACleanup();
		throw NoNetworking();
	}

	struct hostent* phe = gethostbyname(ac);
	if (phe == 0)
	{
		clog(NetWarn) << "Bad host lookup.";
		WSACleanup();
		throw NoNetworking();
	}

	for (int i = 0; phe->h_addr_list[i] != 0; ++i)
	{
		struct in_addr addr;
		memcpy(&addr, phe->h_addr_list[i], sizeof(struct in_addr));
		char *addrStr = inet_ntoa(addr);
		bi::address ad(bi::address::from_string(addrStr));
		m_addresses.push_back(ad.to_v4());
		bool isLocal = std::find(c_rejectAddresses.begin(), c_rejectAddresses.end(), ad) != c_rejectAddresses.end();
		if (!isLocal)
			m_peerAddresses.push_back(ad.to_v4());
		clog(NetNote) << "Address: " << ac << " = " << m_addresses.back() << (isLocal ? " [LOCAL]" : " [PEER]");
	}

	WSACleanup();
#else
	ifaddrs* ifaddr;
	if (getifaddrs(&ifaddr) == -1)
		throw NoNetworking();

	bi::tcp::resolver r(m_ioService);

	for (ifaddrs* ifa = ifaddr; ifa; ifa = ifa->ifa_next)
	{
		if (!ifa->ifa_addr)
			continue;
		if (ifa->ifa_addr->sa_family == AF_INET)
		{
			char host[NI_MAXHOST];
			if (getnameinfo(ifa->ifa_addr, sizeof(struct sockaddr_in), host, NI_MAXHOST, NULL, 0, NI_NUMERICHOST))
				continue;
			try
			{
				auto it = r.resolve({host, "30303"});
				bi::tcp::endpoint ep = it->endpoint();
				bi::address ad = ep.address();
				m_addresses.push_back(ad.to_v4());
				bool isLocal = std::find(c_rejectAddresses.begin(), c_rejectAddresses.end(), ad) != c_rejectAddresses.end();
				if (!isLocal)
					m_peerAddresses.push_back(ad.to_v4());
				clog(NetNote) << "Address: " << host << " = " << m_addresses.back() << (isLocal ? " [LOCAL]" : " [PEER]");
			}
			catch (...)
			{
				clog(NetNote) << "Couldn't resolve: " << host;
			}
		}
	}

	freeifaddrs(ifaddr);
#endif
}

std::map<Public, bi::tcp::endpoint> PeerHost::potentialPeers()
{
	std::map<Public, bi::tcp::endpoint> ret;
	if (!m_public.address().is_unspecified())
		ret.insert(make_pair(m_key.pub(), m_public));
	Guard l(x_peers);
	for (auto i: m_peers)
		if (auto j = i.second.lock())
		{
			auto ep = j->endpoint();
			// Skip peers with a listen port of zero or are on a private network
			bool peerOnNet = (j->m_listenPort != 0 && (!isPrivateAddress(ep.address()) || m_localNetworking));
			if (peerOnNet && ep.port() && j->m_id)
				ret.insert(make_pair(i.first, ep));
		}
	return ret;
}

void PeerHost::ensureAccepting()
{
	if (m_accepting == false)
	{
		clog(NetConnect) << "Listening on local port " << m_listenPort << " (public: " << m_public << ")";
		m_accepting = true;
		m_acceptor.async_accept(m_socket, [=](boost::system::error_code ec)
		{
			if (!ec)
				try
				{
					try {
						clog(NetConnect) << "Accepted connection from " << m_socket.remote_endpoint();
					} catch (...){}
					bi::address remoteAddress = m_socket.remote_endpoint().address();
					// Port defaults to 0 - we let the hello tell us which port the peer listens to
					auto p = std::make_shared<PeerSession>(this, std::move(m_socket), remoteAddress);
					p->start();
				}
				catch (std::exception const& _e)
				{
					clog(NetWarn) << "ERROR: " << _e.what();
				}
			m_accepting = false;
			if (ec.value() != 1)
				ensureAccepting();
		});
	}
}

void PeerHost::connect(std::string const& _addr, unsigned short _port) noexcept
{
	try
	{
		connect(bi::tcp::endpoint(bi::address::from_string(_addr), _port));
	}
	catch (exception const& e)
	{
		// Couldn't connect
		clog(NetConnect) << "Bad host " << _addr << " (" << e.what() << ")";
	}
}

void PeerHost::connect(bi::tcp::endpoint const& _ep)
{
	clog(NetConnect) << "Attempting connection to " << _ep;
	bi::tcp::socket* s = new bi::tcp::socket(m_ioService);
	s->async_connect(_ep, [=](boost::system::error_code const& ec)
	{
		if (ec)
		{
			clog(NetConnect) << "Connection refused to " << _ep << " (" << ec.message() << ")";
			for (auto i = m_incomingPeers.begin(); i != m_incomingPeers.end(); ++i)
				if (i->second.first == _ep && i->second.second < 3)
				{
					m_freePeers.push_back(i->first);
					goto OK;
				}
			// for-else
			clog(NetConnect) << "Giving up.";
			OK:;
		}
		else
		{
			auto p = make_shared<PeerSession>(this, std::move(*s), _ep.address(), _ep.port());
			clog(NetConnect) << "Connected to " << _ep;
			p->start();
		}
		delete s;
	});
}

bool PeerHost::havePeer(Public _id) const
{
	Guard l(x_peers);

	// Remove dead peers from list.
	for (auto i = m_peers.begin(); i != m_peers.end();)
		if (i->second.lock().get())
			++i;
		else
			i = m_peers.erase(i);

	return !!m_peers.count(_id);
}

void PeerHost::growPeers()
{
	Guard l(x_peers);
	while (m_peers.size() < m_idealPeerCount)
	{
		if (m_freePeers.empty())
		{
			if (chrono::steady_clock::now() > m_lastPeersRequest + chrono::seconds(10))
			{
				RLPStream s;
				bytes b;
				(PeerSession::prep(s).appendList(1) << GetPeersPacket).swapOut(b);
				seal(b);
				for (auto const& i: m_peers)
					if (auto p = i.second.lock())
						if (p->isOpen())
							p->send(&b);
				m_lastPeersRequest = chrono::steady_clock::now();
			}


			if (!m_accepting)
				ensureAccepting();

			break;
		}

		auto x = time(0) % m_freePeers.size();
		m_incomingPeers[m_freePeers[x]].second++;
		connect(m_incomingPeers[m_freePeers[x]].first);
		m_freePeers.erase(m_freePeers.begin() + x);
	}
}

void PeerHost::prunePeers()
{
	Guard l(x_peers);
	// We'll keep at most twice as many as is ideal, halfing what counts as "too young to kill" until we get there.
	for (uint old = 15000; m_peers.size() > m_idealPeerCount * 2 && old > 100; old /= 2)
		while (m_peers.size() > m_idealPeerCount)
		{
			// look for worst peer to kick off
			// first work out how many are old enough to kick off.
			shared_ptr<PeerSession> worst;
			unsigned agedPeers = 0;
			for (auto i: m_peers)
				if (auto p = i.second.lock())
					if (/*(m_mode != NodeMode::PeerHost || p->m_caps != 0x01) &&*/ chrono::steady_clock::now() > p->m_connect + chrono::milliseconds(old))	// don't throw off new peers; peer-servers should never kick off other peer-servers.
					{
						++agedPeers;
						if ((!worst || p->m_rating < worst->m_rating || (p->m_rating == worst->m_rating && p->m_connect > worst->m_connect)))	// kill older ones
							worst = p;
					}
			if (!worst || agedPeers <= m_idealPeerCount)
				break;
			worst->disconnect(TooManyPeers);
		}

	// Remove dead peers from list.
	for (auto i = m_peers.begin(); i != m_peers.end();)
		if (i->second.lock().get())
			++i;
		else
			i = m_peers.erase(i);
}

std::vector<PeerInfo> PeerHost::peers(bool _updatePing) const
{
	Guard l(x_peers);
    if (_updatePing)
		const_cast<PeerHost*>(this)->pingAll();
	this_thread::sleep_for(chrono::milliseconds(200));
	std::vector<PeerInfo> ret;
	for (auto& i: m_peers)
		if (auto j = i.second.lock())
			if (j->m_socket.is_open())
				ret.push_back(j->m_info);
	return ret;
}

void PeerHost::process()
{
	for (auto const& i: m_capabilities)
		if (!i.second->isInitialised())
			return;
	growPeers();
	prunePeers();
	m_ioService.poll();
}

void PeerHost::pingAll()
{
	Guard l(x_peers);
	for (auto& i: m_peers)
		if (auto j = i.second.lock())
			j->ping();
}

bytes PeerHost::savePeers() const
{
	Guard l(x_peers);
	RLPStream ret;
	int n = 0;
	for (auto& i: m_peers)
		if (auto p = i.second.lock())
			if (p->m_socket.is_open() && p->endpoint().port())
			{
				ret.appendList(3) << p->endpoint().address().to_v4().to_bytes() << p->endpoint().port() << p->m_id;
				n++;
			}
	return RLPStream(n).appendRaw(ret.out(), n).out();
}

void PeerHost::restorePeers(bytesConstRef _b)
{
	for (auto i: RLP(_b))
	{
		auto k = (Public)i[2];
		if (!m_incomingPeers.count(k))
		{
			m_incomingPeers.insert(make_pair(k, make_pair(bi::tcp::endpoint(bi::address_v4(i[0].toArray<byte, 4>()), i[1].toInt<short>()), 0)));
			m_freePeers.push_back(k);
		}
	}
}
