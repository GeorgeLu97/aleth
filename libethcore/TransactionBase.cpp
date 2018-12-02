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
/** @file TransactionBase.cpp
 * @author Gav Wood <i@gavwood.com>
 * @date 2014
 */

#include <libdevcore/vector_ref.h>
#include <libdevcore/Log.h>
#include <libdevcrypto/Common.h>
#include <libethcore/Exceptions.h>
#include "TransactionBase.h"
#include "EVMSchedule.h"

using namespace std;
using namespace dev;
using namespace dev::eth;

FileData::FileData(bytes b) {
	RLP dataContent(b);
	m_releaseTime = dataContent[0].toInt<uint64_t>();
	m_shareCount = dataContent[1].toInt<uint64_t>();
	m_shareThresh = dataContent[2].toInt<uint64_t>();
	RLP AllPairs = dataContent[3];
	for (uint64_t i = 0; i < m_shareCount; i++) {
		RLP singlePair = AllPairs[i];
		m_candidateList.push_back(make_tuple(Address(singlePair[0].toBytes()), singlePair[1].toBytes(), Signature(singlePair[2].toBytes())));
	}
	m_verifierKey = Public(dataContent[4].toBytes());
	m_encryptedDataHash = dataContent[5].toHash<h256>();
}

FileData::FileData(uint64_t releaseTime, uint64_t shares, uint64_t thresh, vector<Public> candidates, Secret const& secret, bytes const& trueData) : m_releaseTime(releaseTime), m_shareCount(shares), m_shareThresh(thresh)
{
	KeyPair k(Secret::random());
	bytes encryptedData;
	encryptSym(k.secret(), &trueData, encryptedData);
	FileData(releaseTime, shares, thresh, candidates, secret, k.secret(), dev::sha3(encryptedData));
}

FileData::FileData(uint64_t releaseTime, uint64_t shares, uint64_t thresh, std::vector<Public> candidates, Secret const& secret, Secret const& symKey, h256 encryptedDataHash) {
	KeyPair k(Secret::random());
	bytes keyBytes = symKey.makeInsecure().asBytes();
	vector<bytes> secrets;
	m_verifierKey = toPublic(secret);
	m_encryptedDataHash = encryptedDataHash;
	secretShare(thresh, shares, vector_ref<byte const>(&keyBytes), secrets);
	for (uint64_t i = 0; i < shares; i++) {
		bytes encryptedShare;
		encrypt(candidates[i], &secrets[i], encryptedShare);
		SignatureStruct signedShare = dev::sign(secret, dev::sha3(&secrets[i]));
		m_candidateList.push_back(make_tuple(toAddress(candidates[i]), encryptedShare, Signature(signedShare)));
	}
}

bytes FileData::toBytes() {
	RLPStream dataContent;
	dataContent << m_releaseTime << m_shareCount << m_shareThresh;
	RLPStream AllPairs;

	for (uint64_t i = 0; i < m_shareCount; i++) {
		RLPStream singlePair;
		singlePair << get<0>(m_candidateList[i]).asBytes() << get<1>(m_candidateList[i]) << get<2>(m_candidateList[i]).asBytes();
		AllPairs << singlePair.out();
	}
	dataContent << AllPairs.out() << m_verifierKey.ref() << m_encryptedDataHash;
	return dataContent.out();
}

KeyData::KeyData(bytes b) {
	RLP keyContent(b);
	m_shareData = keyContent[0].toBytes();
	m_shareIndex = keyContent[1].toInt<u256>();
	m_releaseCert = h256(keyContent[2].toBytes());
}

bytes KeyData::toBytes() {
	RLPStream keyContent;
	keyContent << m_shareData << m_shareIndex << m_releaseCert.asBytes();
	return keyContent.out();
}

TransactionBase::TransactionBase(TransactionSkeleton const& _ts, Secret const& _s):
	m_type(_ts.creation ? ContractCreation : MessageCall),
	m_nonce(_ts.nonce),
	m_value(_ts.value),
	m_receiveAddress(_ts.to),
	m_gasPrice(_ts.gasPrice),
	m_gas(_ts.gas),
	m_data(_ts.data),
	m_sender(_ts.from)
{
	if (_s)
		sign(_s);
}

TransactionBase::TransactionBase(bytesConstRef _rlpData, CheckTransaction _checkSig)
{
	RLP const rlp(_rlpData);
	try
	{
		if (!rlp.isList())
			BOOST_THROW_EXCEPTION(InvalidTransactionFormat() << errinfo_comment("transaction RLP must be a list"));

		m_nonce = rlp[0].toInt<u256>();
		m_gasPrice = rlp[1].toInt<u256>();
		m_gas = rlp[2].toInt<u256>();
		m_type = static_cast<Type>(rlp[3].toInt<u256>());
		m_receiveAddress = (m_type != MessageCall && m_type != KeyPublish) ? Address() : rlp[4].toHash<Address>(RLP::VeryStrict);
		m_value = rlp[5].toInt<u256>();

		if (!rlp[6].isData())
			BOOST_THROW_EXCEPTION(InvalidTransactionFormat() << errinfo_comment("transaction data RLP must be an array"));

		m_data = rlp[6].toBytes();

		int const v = rlp[7].toInt<int>();
		h256 const r = rlp[8].toInt<u256>();
		h256 const s = rlp[9].toInt<u256>();

		if (isZeroSignature(r, s))
		{
			m_chainId = v;
			m_vrs = SignatureStruct{r, s, 0};
		}
		else
		{
			if (v > 36)
				m_chainId = (v - 35) / 2; 
			else if (v == 27 || v == 28)
				m_chainId = -4;
			else
				BOOST_THROW_EXCEPTION(InvalidSignature());

			m_vrs = SignatureStruct{r, s, static_cast<byte>(v - (m_chainId * 2 + 35))};

			if (_checkSig >= CheckTransaction::Cheap && !m_vrs->isValid())
				BOOST_THROW_EXCEPTION(InvalidSignature());
		}

		if (_checkSig == CheckTransaction::Everything)
			m_sender = sender();

		if (rlp.itemCount() > 9)
			BOOST_THROW_EXCEPTION(InvalidTransactionFormat() << errinfo_comment("too many fields in the transaction RLP"));
	}
	catch (Exception& _e)
	{
		_e << errinfo_name("invalid transaction format: " + toString(rlp) + " RLP: " + toHex(rlp.data()));
		throw;
	}
}


/*
 * Constructor 1:  TransactionBase 
 * ----------------------
 * Add Key + File transactions
 *
 *  _value: transaction amount
 *	_gasPrice: gas price per step
 *  _gas: gas provided 
 *	_dest: destination address of file/key
 *  _shareData: data to be stored
 *	ind: index of the secret
 *  releaseCert: signature
 *  _nonce: nonce for the transaction
 */

TransactionBase::TransactionBase(u256 const& _value, u256 const& _gasPrice, u256 const& _gas, Address const& _dest, 
	bytes const& _shareData, u256 ind, h256 releaseCert, 
	u256 const& _nonce = 0) 
	: m_type(KeyPublish), m_nonce(_nonce), m_value(_value), m_receiveAddress(_dest), m_gasPrice(_gasPrice), m_gas(_gas) 
{
	KeyData k(_shareData, ind, releaseCert);
	m_data = k.toBytes();
}

///Key Release
// Previous with a signature

/*
 * Constructor 2:  TransactionBase 
 * ----------------------
 * Add Key + File transactions with a signature
 *
 *  _value: transaction amount
 *	_gasPrice: gas price per step
 *  _gas: gas provided 
 *	_dest: destination address of file/key
 *  _shareData: data to be stored
 *	ind: index of the secret
 *  releaseCert: signature
 *  _nonce: nonce for the transaction
 * 	_secret: key used to sign
 */

TransactionBase::TransactionBase(u256 const& _value, u256 const& _gasPrice, u256 const& _gas, Address const& _dest, 
	bytes const& _shareData, u256 ind, h256 releaseCert, 
	u256 const& _nonce, Secret const& _secret) : TransactionBase::TransactionBase(_value, _gasPrice, _gas, _dest, _shareData, ind, releaseCert, _nonce) {
	sign(_secret);
}

/// Constructs a signed FilePublish transaction.
///include encrypted data, account - symmetric key encrypted secret share, encrypted? signature. 
///Key for shares is auto randomized.

///m_data[0] = { releaseTime[0], shares[1], thresh[2], allpairs[3], publicKey[4], encryptedData[5] }
///shares = { address[0], share[1], r[2], s[3], v[4] }

/*
 * Constructor 3:  TransactionBase 
 * ----------------------
 * Constructs a signed FilePublish transaction.
 *
 *  _value: transaction amount
 *	_gasPrice: gas price per step
 *  _gas: gas provided 
 *  _data: data to for the transaction
 *  releaseTime: time to release the FilePublish transaction
 *  shares: number of shares
 *  threshold: min secrets required to recover msg
 *	candidates: list a public keys to split secret 
 *  _nonce: nonce for the transaction
 * 	_secret: key used to sign
 */
TransactionBase::TransactionBase(u256 const& _value, u256 const& _gasPrice, u256 const& _gas, bytes const& _data, 
	uint64_t releaseTime, uint64_t shares, uint64_t threshold, vector<Public> const& candidates,  
	u256 const& _nonce, Secret const& _secret)
	: m_type(FilePublish), m_nonce(_nonce), m_value(_value), m_gasPrice(_gasPrice), m_gas(_gas)  {
	// Building the byte stream to push data out
	RLPStream dataContent;
	FileData f(releaseTime, shares, threshold, candidates, _secret, _data);
	m_data = f.toBytes();
	sign(_secret);
}

TransactionBase::TransactionBase(u256 const& _value, u256 const& _gasPrice, u256 const& _gas, h256 _datahash,
	uint64_t releaseTime, uint64_t shares, uint64_t threshold, std::vector<Public> const& candidates,
	u256 const& _nonce, Secret const& _secret, Secret const& symKey) : m_type(FilePublish), m_nonce(_nonce), m_value(_value), m_gasPrice(_gasPrice), m_gas(_gas) {
	// Building the byte stream to push data out
	RLPStream dataContent;
	FileData f(releaseTime, shares, threshold, candidates, _secret, symKey, _datahash);
	m_data = f.toBytes();
	sign(_secret);
}

Address const& TransactionBase::safeSender() const noexcept
{
	try
	{
		return sender();
	}
	catch (...)
	{
		return ZeroAddress;
	}
}

Address const& TransactionBase::sender() const
{
	if (!m_sender)
	{
		if (hasZeroSignature())
			m_sender = MaxAddress;
		else
		{
			if (!m_vrs)
				BOOST_THROW_EXCEPTION(TransactionIsUnsigned());

			auto p = recover(*m_vrs, sha3(WithoutSignature));
			if (!p)
				BOOST_THROW_EXCEPTION(InvalidSignature());
			m_sender = right160(dev::sha3(bytesConstRef(p.data(), sizeof(p))));
		}
	}
	return m_sender;
}

SignatureStruct const& TransactionBase::signature() const
{ 
	if (!m_vrs)
		BOOST_THROW_EXCEPTION(TransactionIsUnsigned());

	return *m_vrs;
}

void TransactionBase::sign(Secret const& _priv)
{
	auto sig = dev::sign(_priv, sha3(WithoutSignature));
	SignatureStruct sigStruct = *(SignatureStruct const*)&sig;
	if (sigStruct.isValid())
		m_vrs = sigStruct;
}

void TransactionBase::streamRLP(RLPStream& _s, IncludeSignature _sig, bool _forEip155hash) const
{
	if (m_type == NullTransaction)
		return;

	_s.appendList((_sig || _forEip155hash ? 3 : 0) + 6);
	_s << m_nonce << m_gasPrice << m_gas;
	_s << static_cast<u256>(m_type);
	if (m_type == MessageCall || m_type == KeyPublish)
		_s << m_receiveAddress;
	else
		_s << "";
	_s << m_value << m_data;

	if (_sig)
	{
		if (!m_vrs)
			BOOST_THROW_EXCEPTION(TransactionIsUnsigned());

		if (hasZeroSignature())
			_s << m_chainId;
		else
		{
			int const vOffset = m_chainId * 2 + 35;
			_s << (m_vrs->v + vOffset);
		}
		_s << (u256)m_vrs->r << (u256)m_vrs->s;
	}
	else if (_forEip155hash)
		_s << m_chainId << 0 << 0;
}

static const u256 c_secp256k1n("115792089237316195423570985008687907852837564279074904382605163141518161494337");

void TransactionBase::checkLowS() const
{
	if (!m_vrs)
		BOOST_THROW_EXCEPTION(TransactionIsUnsigned());

	if (m_vrs->s > c_secp256k1n / 2)
		BOOST_THROW_EXCEPTION(InvalidSignature());
}

void TransactionBase::checkChainId(int chainId) const
{
	if (m_chainId != chainId && m_chainId != -4)
		BOOST_THROW_EXCEPTION(InvalidSignature());
}

int64_t TransactionBase::baseGasRequired(bool _contractCreation, bytesConstRef _data, EVMSchedule const& _es)
{
	int64_t g = _contractCreation ? _es.txCreateGas : _es.txGas;

	// Calculate the cost of input data.
	// No risk of overflow by using int64 until txDataNonZeroGas is quite small
	// (the value not in billions).
	for (auto i: _data)
		g += i ? _es.txDataNonZeroGas : _es.txDataZeroGas;
	return g;
}

h256 TransactionBase::sha3(IncludeSignature _sig) const
{
	if (_sig == WithSignature && m_hashWith)
		return m_hashWith;

	RLPStream s;
	streamRLP(s, _sig, m_chainId > 0 && _sig == WithoutSignature);

	auto ret = dev::sha3(s.out());
	if (_sig == WithSignature)
		m_hashWith = ret;
	return ret;
}
